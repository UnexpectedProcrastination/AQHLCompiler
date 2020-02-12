#include "Basic.h"
#include "Optimizer.h"
#include "CodeGenerator.h"
#include "ArraySet.h"
#include "CompilerMain.h"

WorkQueue<DeclFunction *> optimizerQueue;

static bool operator==(const Constraint a, const Constraint b) {
	return a.min == b.min && a.max == b.max;
}

static bool operator!=(const Constraint a, const Constraint b) {
	return !(a == b);
}

static const Reg regNone = { nullptr, 0, RegType::NONE };

u64 NUM_OPTIMIZER_THREADS = 1;

bool opIsBoolean(AstType type) {
	switch (type) {
		case AstType::EQUAL:
		case AstType::GREATER:
		case AstType::LESS:
		case AstType::UGREATER:
		case AstType::ULESS:
			return true;
		default:
			return false;
	}
}

struct Compiler {

	Array<Array<u32>> breaks;
	Array<u32> loopStarts;

	u32 breaksIndex = 0;
	ulang nextRegister;
	ulang argCount = 0;

	void generateIr(DeclFunction *function);
	Reg compile(Reg dest, AstNode *node, Array<Ir> &ops);
	u32 compileIf(AstNode *node, Array<Ir> &ops, IrType op);
	Reg compileEq(Reg dest, AstNode *lhs, AstNode *rhs, Array<Ir> &ops);

	void pushBreak() {
		if (++breaksIndex > breaks.size()) {
			breaks.add();
		}
	}

	Array<u32> &getBreak() {
		return breaks[breaksIndex - 1];
	}

	void popBreak() {
		--breaksIndex;
		breaks[breaksIndex].clear();
	}

};

void recursiveFree(AstNode *node) {
	if (node->flags & AST_IS_TREE) {
		AstTreeNode *tree = static_cast<AstTreeNode *>(node);

		for (auto child : tree->children) {
			recursiveFree(child);
		}

		tree->children.free();
	}
}

void Compiler::generateIr(DeclFunction *function) {
	PROFILE_FUNC();
	assert(!(function->flags & DECL_IS_EXTERN));

	assert(!breaksIndex);
	assert(!loopStarts.size());
	assert(!function->ops.size());
	assert(function->body);

	argCount = nextRegister = static_cast<ulang>(function->arguments.size());

	for (auto argument : function->arguments) {
		argument->flags |= AST_VAR_HAS_REGISTER_ASSIGNED;
		argument->text.free();
	}
	function->arguments.free();

	compile(regNone, function->body, function->ops);

	{
		PROFILE_ZONE("recursiveFree");
		recursiveFree(function->body);
	}

	function->astNodeAllocator.free();
}

static Reg reg(ulang num) {
	Reg result;
	result.unumber = num;
	result.type = RegType::REGISTER;

	return result;
}

static Reg global(Decl *decl) {
	Reg result;
	result.decl = decl;
	result.number = 0;
	result.type = RegType::STATIC_ADROF;

	return result;
}

static Reg literal(slang number) {
	Reg result;
	result.decl = nullptr;
	result.number = number;
	result.type = RegType::IMMEDIATE;

	return result;
}

static bool nodeIsLiteral(AstNode *node, slang value) {
	return !(node->flags & AST_IS_TREE) &&
		node->type == AstType::INT_LITERAL &&
		static_cast<AstLeafNode *>(node)->number == value;
}

static void changeToNoop(Ir &op) {
	if (op.type == IrType::CALL) 
		op.callRegs.free();

	op.dest = regNone;
	op.regCount = 0;
	op.type = IrType::NOOP;
}

Reg Compiler::compileEq(Reg dest, AstNode *lhs, AstNode *rhs, Array<Ir> &ops) {
	assert(dest);

	IrType op = IrType::EQ;

	while (true) {
		if (nodeIsLiteral(lhs, 0)) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(rhs);

			switch (tree->type) {
				case AstType::EQUAL:
					op = op == IrType::EQ ? IrType::NOT_EQ : IrType::EQ;

					lhs = tree->children[0];
					rhs = tree->children[1];
					continue;
				case AstType::GREATER:
					op = op == IrType::EQ ? IrType::LESS_EQUAL : IrType::GREATER;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::LESS:
					op = op == IrType::EQ ? IrType::GREATER_EQUAL : IrType::LESS;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::UGREATER:
					op = op == IrType::EQ ? IrType::BELOW_EQUAL : IrType::ABOVE;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::ULESS:
					op = op == IrType::EQ ? IrType::ABOVE_EQUAL : IrType::BELOW;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
			}

			break;
		}
		else if (nodeIsLiteral(rhs, 0)) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(lhs);

			switch (tree->type) {
				case AstType::EQUAL:
					op = op == IrType::EQ ? IrType::NOT_EQ : IrType::EQ;

					lhs = tree->children[0];
					rhs = tree->children[1];
					continue;
				case AstType::GREATER:
					op = op == IrType::EQ ? IrType::LESS_EQUAL : IrType::GREATER;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::LESS:
					op = op == IrType::EQ ? IrType::GREATER_EQUAL : IrType::LESS;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::UGREATER:
					op = op == IrType::EQ ? IrType::BELOW_EQUAL : IrType::ABOVE;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::ULESS:
					op = op == IrType::EQ ? IrType::ABOVE_EQUAL : IrType::BELOW;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
			}

			break;
		}
		else if (nodeIsLiteral(lhs, 1)) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(rhs);

			switch (tree->type) {
				case AstType::EQUAL:
					op = op == IrType::NOT_EQ ? IrType::NOT_EQ : IrType::EQ;

					lhs = tree->children[0];
					rhs = tree->children[1];
					continue;
				case AstType::GREATER:
					op = op == IrType::NOT_EQ ? IrType::LESS_EQUAL : IrType::GREATER;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::LESS:
					op = op == IrType::NOT_EQ ? IrType::GREATER_EQUAL : IrType::LESS;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::UGREATER:
					op = op == IrType::NOT_EQ ? IrType::BELOW_EQUAL : IrType::ABOVE;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::ULESS:
					op = op == IrType::NOT_EQ ? IrType::ABOVE_EQUAL : IrType::BELOW;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
			}

			break;
		}
		else if (nodeIsLiteral(rhs, 1)) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(lhs);

			switch (tree->type) {
				case AstType::EQUAL:
					op = op == IrType::NOT_EQ ? IrType::NOT_EQ : IrType::EQ;

					lhs = tree->children[0];
					rhs = tree->children[1];
					continue;
				case AstType::GREATER:
					op = op == IrType::NOT_EQ ? IrType::LESS_EQUAL : IrType::GREATER;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::LESS:
					op = op == IrType::NOT_EQ ? IrType::GREATER_EQUAL : IrType::LESS;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::UGREATER:
					op = op == IrType::NOT_EQ ? IrType::BELOW_EQUAL : IrType::ABOVE;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
				case AstType::ULESS:
					op = op == IrType::NOT_EQ ? IrType::ABOVE_EQUAL : IrType::BELOW;

					lhs = tree->children[0];
					rhs = tree->children[1];
					break;
			}

			break;
		}

		break;
	}

	Reg storeA = compile(reg(nextRegister++), lhs, ops);
	assert(storeA);

	Reg storeB = compile(reg(nextRegister++), rhs, ops);
	assert(storeB);

	Ir &ir = ops.add();
	ir.type = op;
	ir.dest = dest;
	ir.regs[0] = storeA;
	ir.regs[1] = storeB;
	ir.regCount = 2;

	return dest;
}

u32 Compiler::compileIf(AstNode *node, Array<Ir> &ops, IrType op) {

	bool innerEqIsOne = false;

	while (true) {
		AstTreeNode *tree = static_cast<AstTreeNode *>(node);
		switch (node->type) {
			case AstType::EQUAL:
				if (nodeIsLiteral(tree->children[0], 0)) {
					op = op == IrType::IF_Z ? IrType::IF_NZ : IrType::IF_Z;
					node = tree->children[1];
					continue;
				}
				else if (nodeIsLiteral(tree->children[1], 0)) {
					op = op == IrType::IF_Z ? IrType::IF_NZ : IrType::IF_Z;
					node = tree->children[0];
					continue;
				}
				else if (nodeIsLiteral(tree->children[0], 1) && opIsBoolean(tree->children[1]->type)) {
					node = tree->children[1];
					continue;
				}
				else if (nodeIsLiteral(tree->children[1], 1) && opIsBoolean(tree->children[0]->type)) {
					node = tree->children[0];
					continue;
				}
				else {
					op = op == IrType::IF_Z ? IrType::IF_NEQ : IrType::IF_EQ;
					break;
				}
			case AstType::GREATER:
				op = op == IrType::IF_Z ? IrType::IF_LE : IrType::IF_G;
				break;
			case AstType::LESS:
				op = op == IrType::IF_Z ? IrType::IF_GE : IrType::IF_L;
				break;
			case AstType::UGREATER:
				op = op == IrType::IF_Z ? IrType::IF_BE : IrType::IF_A;
				break;
			case AstType::ULESS:
				op = op == IrType::IF_Z ? IrType::IF_AE : IrType::IF_B;
				break;
			case AstType::BIT_AND:
				op = op == IrType::IF_Z ? IrType::IF_AND_Z : IrType::IF_AND_NZ;
				break;
		}

		break;
	}

	u32 result;

	if (op == IrType::IF_Z || op == IrType::IF_NZ) {
		Reg store = compile(reg(nextRegister++), node, ops);
		assert(store);

		result = ops.size();

		Ir &branch = ops.add();
		branch.type = op;
		branch.regs[0] = store;
		branch.regCount = 1;
	}
	else {
		AstTreeNode *tree = static_cast<AstTreeNode *>(node);

		Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
		assert(storeA);

		Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
		assert(storeB);

		result = ops.size();

		Ir &branch = ops.add();
		branch.type = op;
		branch.regs[0] = storeA;
		branch.regs[1] = storeB;

		branch.regCount = 2;
	}

	return result;
}

static bool isCompare(AstType type) {
	switch (type) {
		case AstType::EQUAL:
		case AstType::GREATER:
		case AstType::LESS:
		case AstType::UGREATER:
		case AstType::ULESS:
			return true;
		default:
			return false;
	}
}

Reg Compiler::compile(Reg dest, AstNode *node, Array<Ir> &ops) {
	AstTreeNode *tree = static_cast<AstTreeNode *>(node);
	AstLeafNode *leaf = static_cast<AstLeafNode *>(node);

	Reg storedIn = regNone;

	switch (node->type) {
		case AstType::NOOP: {
			assert(!dest);
			break;
		} case AstType::VAR_DECL: {
			assert(!dest);

			if (!(leaf->flags & AST_VAR_HAS_REGISTER_ASSIGNED)) {
				leaf->flags |= AST_VAR_HAS_REGISTER_ASSIGNED;
				leaf->unumber = nextRegister++;
			}
			break;
		}
		case AstType::LOCAL_VAR: {
			assert(leaf->localIdent->flags & AST_VAR_HAS_REGISTER_ASSIGNED);

			storedIn = reg(leaf->localIdent->unumber);
			break;
		}
		case AstType::GLOBAL_POINTER: {
			storedIn = global(leaf->globalIdent);
			break;
		}
		case AstType::LOOP: {
			assert(!dest);

			loopStarts.add(ops.size());
			pushBreak();

			u32 branchIndex = compileIf(tree->children[0], ops, IrType::IF_Z);

			getBreak().add(branchIndex);

			u32 loopStart = ops.size();

			compile(regNone, tree->children[1], ops);

			branchIndex = compileIf(tree->children[0], ops, IrType::IF_NZ);
			ops[branchIndex].jumpTarget = loopStart;

			loopStarts.pop();

			for (u32 branch : getBreak()) {
				ops[branch].jumpTarget = ops.size();
			}

			popBreak();

			break;
		}
		case AstType::BREAK: {
			assert(!dest);

			getBreak().add(ops.size());

			Ir &jump = ops.add();

			jump.type = IrType::GOTO;

			break;
		}
		case AstType::CONTINUE: {
			assert(!dest);

			Ir &jump = ops.add();

			jump.type = IrType::GOTO;
			jump.jumpTarget = loopStarts[loopStarts.size() - 1];

			break;
		}
		case AstType::IF_ELSE: {
			assert(!dest);

			u32 branch = compileIf(tree->children[0], ops, IrType::IF_Z);

			compile(regNone, tree->children[1], ops);

			if (tree->children.size() == 2) {
				ops[branch].jumpTarget = ops.size();
			}
			else {
				assert(tree->children.size() == 3);

				u32 index = ops.size();
				Ir &jump = ops.add();
				jump.type = IrType::GOTO;

				ops[branch].jumpTarget = ops.size();

				compile(regNone, tree->children[2], ops);

				ops[index].jumpTarget = ops.size();
			}

			break;
		}
		case AstType::TERNARY: {
			u32 branch = compileIf(tree->children[0], ops, IrType::IF_Z);

			Reg store = compile(dest, tree->children[1], ops);

			if (dest) {
				assert(store);
				if (store != dest) {
					Ir &move = ops.add();
					move.type = IrType::SET;
					move.dest = dest;
					move.regCount = 1;
					move.regs[0] = store;
				}
			}

			assert(tree->children.size() == 3);

			u32 index = ops.size();
			Ir &jump = ops.add();
			jump.type = IrType::GOTO;

			ops[branch].jumpTarget = ops.size();

			store = compile(dest, tree->children[2], ops);

			if (dest) {
				assert(store);
				if (store != dest) {
					Ir &move = ops.add();
					move.type = IrType::SET;
					move.dest = dest;
					move.regCount = 1;
					move.regs[0] = store;
				}
			}

			ops[index].jumpTarget = ops.size();

			storedIn = dest;

			break;
		}
		case AstType::RETURN: {
			assert(!dest);

			if (node->flags & AST_IS_TREE) {
				Reg store = compile(reg(nextRegister++), tree->children[0], ops);
				assert(store);

				Ir &ret = ops.add();
				ret.type = IrType::RETURN;
				ret.regs[0] = store;
				ret.regCount = 1;
			}
			else {
				Ir &ret = ops.add();
				ret.type = IrType::RETURN;
			}

			break;
		}
		case AstType::L_AND: {
			SmallArray<u32, 32> branches;
			SmallArray<u32, 32> literalBranches;

			if (dest) {
				for (u32 i = 0; i < tree->children.size(); i++) {
					if (isCompare(tree->children[i]->type)) {
						u32 index = compileIf(tree->children[i], ops, IrType::IF_Z);
						literalBranches.add(index);

						if (i == tree->children.size() - 1) {
							Ir &move = ops.add();
							move.type = IrType::SET;
							move.dest = dest;
							move.regs[0] = literal(1);
							move.regCount = 1;

							Ir &skipZero = ops.add();
							skipZero.type = IrType::GOTO;
							skipZero.dest = regNone;
							skipZero.jumpTarget = ops.size() + 1;
							skipZero.regCount = 0;
						}
					}
					else {
						Reg store = compile(dest, tree->children[i], ops);

						assert(store);

						if (store != dest) {
							Ir &move = ops.add();
							move.type = IrType::SET;
							move.dest = dest;
							move.regs[0] = store;
							move.regCount = 1;
						}

						if (i != tree->children.size() - 1) {
							branches.add(ops.size());
							Ir &branch = ops.add();
							branch.type = IrType::IF_Z;
							branch.regs[0] = dest;
							branch.regCount = 1;
						}

						if (i == tree->children.size() - 1 && literalBranches.size()) {
							Ir &skipZero = ops.add();
							skipZero.type = IrType::GOTO;
							skipZero.dest = regNone;
							skipZero.jumpTarget = ops.size() + 1;
							skipZero.regCount = 0;
						}
					}
				}

				storedIn = dest;
			}
			else {
				for (u32 i = 0; i < tree->children.size(); i++) {
					if (i != tree->children.size() - 1) {
						branches.add(compileIf(tree->children[i], ops, IrType::IF_Z));
					}
					else {
						compile(regNone, tree->children[i], ops);
					}
				}
			}

			if (literalBranches.size()) {
				for (u32 branch : literalBranches) {
					ops[branch].jumpTarget = ops.size();
				}

				Ir &move = ops.add();
				move.type = IrType::SET;
				move.dest = dest;
				move.regs[0] = literal(0);
				move.regCount = 1;
			}

			for (u32 branch : branches) {
				ops[branch].jumpTarget = ops.size();
			}

			literalBranches.free();
			branches.free();
			break;
		}
		case AstType::L_OR: {
			SmallArray<u32, 32> branches;
			SmallArray<u32, 32> literalBranches;

			if (dest) {
				for (u32 i = 0; i < tree->children.size(); i++) {
					if (isCompare(tree->children[i]->type)) {
						u32 index = compileIf(tree->children[i], ops, IrType::IF_NZ);
						literalBranches.add(index);

						if (i == tree->children.size() - 1) {
							Ir &move = ops.add();
							move.type = IrType::SET;
							move.dest = dest;
							move.regs[0] = literal(0);
							move.regCount = 1;

							Ir &skipOne = ops.add();
							skipOne.type = IrType::GOTO;
							skipOne.dest = regNone;
							skipOne.jumpTarget = ops.size() + 1;
							skipOne.regCount = 0;
						}
					}
					else {
						Reg store = compile(dest, tree->children[i], ops);

						assert(store);

						if (store != dest) {
							Ir &move = ops.add();
							move.type = IrType::SET;
							move.dest = dest;
							move.regs[0] = store;
							move.regCount = 1;
						}

						if (i != tree->children.size() - 1) {
							branches.add(ops.size());
							Ir &branch = ops.add();
							branch.type = IrType::IF_NZ;
							branch.regs[0] = dest;
							branch.regCount = 1;
						}

						if (i == tree->children.size() - 1 && literalBranches.size()) {
							Ir &skipOne = ops.add();
							skipOne.type = IrType::GOTO;
							skipOne.dest = regNone;
							skipOne.jumpTarget = ops.size() + 1;
							skipOne.regCount = 0;
						}
					}
				}

				storedIn = dest;
			}
			else {
				for (u32 i = 0; i < tree->children.size(); i++) {
					if (i != tree->children.size() - 1) {
						branches.add(compileIf(tree->children[i], ops, IrType::IF_NZ));
					}
					else {
						compile(regNone, tree->children[i], ops);
					}
				}
			}

			if (literalBranches.size()) {
				for (u32 branch : literalBranches) {
					ops[branch].jumpTarget = ops.size();
				}

				Ir &move = ops.add();
				move.type = IrType::SET;
				move.dest = dest;
				move.regs[0] = literal(1);
				move.regCount = 1;
			}

			for (u32 branch : branches) {
				ops[branch].jumpTarget = ops.size();
			}

			literalBranches.free();
			branches.free();
			break;
		}
		case AstType::SEQUENCE: {
			for (u32 i = 0; i < tree->children.size(); i++) {
				if (i != tree->children.size() - 1) {
					compile(regNone, tree->children[i], ops);
				}
				else {
					Reg store = compile(dest, tree->children[i], ops);

					assert(!dest || store);

					storedIn = store;
				}
			}

			break;
		}
		case AstType::NEG: {
			if (dest) {
				Reg store = compile(reg(nextRegister++), tree->children[0], ops);
				assert(store);


				Ir &neg = ops.add();
				neg.type = IrType::NEG;
				neg.dest = dest;
				neg.regs[0] = store;
				neg.regCount = 1;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::BIT_NOT: {
			if (dest) {
				Reg store = compile(reg(nextRegister++), tree->children[0], ops);
				assert(store);


				Ir & not = ops.add();
				not.type = IrType::NOT;
				not.dest = dest;
				not.regs[0] = store;
				not.regCount = 1;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::DEREF: {
			if (dest) {
				Reg store = compile(reg(nextRegister++), tree->children[0], ops);
				assert(store);


				Ir &read = ops.add();
				read.type = IrType::READ;
				read.dest = dest;
				read.regs[0] = store;
				read.regCount = 1;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::ADD: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				if (tree->children[1]->type == AstType::NEG) {
					AstTreeNode *neg = static_cast<AstTreeNode *>(tree->children[1]);

					Reg storeB = compile(reg(nextRegister++), neg->children[0], ops);
					assert(storeB);

					Ir &sub = ops.add();
					sub.type = IrType::SUB;
					sub.dest = dest;
					sub.regs[0] = storeA;
					sub.regs[1] = storeB;
					sub.regCount = 2;
				}
				else {
					Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
					assert(storeB);

					Ir &add = ops.add();
					add.type = IrType::ADD;
					add.dest = dest;
					add.regs[0] = storeA;
					add.regs[1] = storeB;
					add.regCount = 2;
				}

				if (tree->children.size() > 2) {

					for (u32 i = 2; i < tree->children.size(); i++) {
						if (tree->children[i]->type == AstType::NEG) {
							AstTreeNode *neg = static_cast<AstTreeNode *>(tree->children[i]);

							Reg store = compile(reg(nextRegister++), neg->children[0], ops);
							assert(store);

							Ir &sub = ops.add();
							sub.type = IrType::SUB;
							sub.dest = dest;
							sub.regs[0] = dest;
							sub.regs[1] = store;
							sub.regCount = 2;
						}
						else {
							Reg store = compile(reg(nextRegister++), tree->children[i], ops);
							assert(store);

							Ir &add = ops.add();
							add.type = IrType::ADD;
							add.dest = dest;
							add.regs[0] = dest;
							add.regs[1] = store;
							add.regCount = 2;
						}
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::SUB: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				if (tree->children[1]->type == AstType::NEG) {
					AstTreeNode *neg = static_cast<AstTreeNode *>(tree->children[1]);

					Reg storeB = compile(reg(nextRegister++), neg->children[0], ops);
					assert(storeB);

					Ir &add = ops.add();
					add.type = IrType::ADD;
					add.dest = dest;
					add.regs[0] = storeA;
					add.regs[1] = storeB;
					add.regCount = 2;
				}
				else {
					Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
					assert(storeB);

					Ir &sub = ops.add();
					sub.type = IrType::SUB;
					sub.dest = dest;
					sub.regs[0] = storeA;
					sub.regs[1] = storeB;
					sub.regCount = 2;
				}

				if (tree->children.size() > 2) {

					for (u32 i = 2; i < tree->children.size(); i++) {
						if (tree->children[i]->type == AstType::NEG) {
							AstTreeNode *neg = static_cast<AstTreeNode *>(tree->children[i]);

							Reg store = compile(reg(nextRegister++), neg->children[0], ops);
							assert(store);

							Ir &add = ops.add();
							add.type = IrType::ADD;
							add.dest = dest;
							add.regs[0] = dest;
							add.regs[1] = store;
							add.regCount = 2;
						}
						else {
							Reg store = compile(reg(nextRegister++), tree->children[i], ops);
							assert(store);

							Ir &sub = ops.add();
							sub.type = IrType::SUB;
							sub.dest = dest;
							sub.regs[0] = dest;
							sub.regs[1] = store;
							sub.regCount = 2;
						}
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::MUL: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				{
					Ir &mul = ops.add();
					mul.type = IrType::MUL;
					mul.dest = dest;
					mul.regs[0] = storeA;
					mul.regs[1] = storeB;
					mul.regCount = 2;
				}

				if (tree->children.size() > 2) {
					for (u32 i = 2; i < tree->children.size(); i++) {
						Reg store = compile(reg(nextRegister++), tree->children[i], ops);
						assert(store);

						Ir &mul = ops.add();
						mul.type = IrType::MUL;
						mul.dest = dest;
						mul.regs[0] = dest;
						mul.regs[1] = store;
						mul.regCount = 2;
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::DIV: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &div = ops.add();
				div.type = IrType::DIV;
				div.dest = dest;
				div.regs[0] = storeA;
				div.regs[1] = storeB;
				div.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::MOD: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &mod = ops.add();
				mod.type = IrType::MOD;
				mod.dest = dest;
				mod.regs[0] = storeA;
				mod.regs[1] = storeB;
				mod.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::EQUAL: {
			if (dest) {
				Reg store = compileEq(dest, tree->children[0], tree->children[1], ops);

				assert(store);
				storedIn = store;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::GREATER: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::GREATER;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::UGREATER: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::ABOVE;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::LESS: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::LESS;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::ULESS: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::BELOW;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::LSHIFT: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::LSHIFT;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::RSHIFT: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::ARSHIFT;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::URSHIFT: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &op = ops.add();
				op.type = IrType::RSHIFT;
				op.dest = dest;
				op.regs[0] = storeA;
				op.regs[1] = storeB;
				op.regCount = 2;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::BIT_AND: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				{
					Ir &op = ops.add();
					op.type = IrType::AND;
					op.dest = dest;
					op.regs[0] = storeA;
					op.regs[1] = storeB;
					op.regCount = 2;
				}

				if (tree->children.size() > 2) {
					for (u32 i = 2; i < tree->children.size(); i++) {
						Reg store = compile(reg(nextRegister++), tree->children[i], ops);
						assert(store);

						Ir &op = ops.add();
						op.type = IrType::AND;
						op.dest = dest;
						op.regs[0] = dest;
						op.regs[1] = store;
						op.regCount = 2;
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::BIT_OR: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				{
					Ir &op = ops.add();
					op.type = IrType::OR;
					op.dest = dest;
					op.regs[0] = storeA;
					op.regs[1] = storeB;
					op.regCount = 2;
				}

				if (tree->children.size() > 2) {
					for (u32 i = 2; i < tree->children.size(); i++) {
						Reg store = compile(reg(nextRegister++), tree->children[i], ops);
						assert(store);

						Ir &op = ops.add();
						op.type = IrType::OR;
						op.dest = dest;
						op.regs[0] = dest;
						op.regs[1] = store;
						op.regCount = 2;
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::XOR: {
			if (dest) {
				Reg storeA = compile(reg(nextRegister++), tree->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				{
					Ir &op = ops.add();
					op.type = IrType::XOR;
					op.dest = dest;
					op.regs[0] = storeA;
					op.regs[1] = storeB;
					op.regCount = 2;
				}

				if (tree->children.size() > 2) {
					for (u32 i = 2; i < tree->children.size(); i++) {
						Reg store = compile(reg(nextRegister++), tree->children[i], ops);
						assert(store);

						Ir &op = ops.add();
						op.type = IrType::XOR;
						op.dest = dest;
						op.regs[0] = dest;
						op.regs[1] = store;
						op.regCount = 2;
					}
				}

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::CALL: {
			decltype(Ir::callRegs) regs(tree->children.size());

			for (auto child : tree->children) {
				Reg store = compile(reg(nextRegister++), child, ops);
				assert(store);
				regs.add(store);
			}

			Ir &call = ops.add();
			call.callRegs = regs;
			call.regCount = static_cast<ulang>(regs.size());
			call.type = IrType::CALL;
			call.dest = dest;

			storedIn = dest;

			break;
		}
		case AstType::ARRAY: {
			if (dest) {
				Reg store = compile(reg(nextRegister++), tree->children[0], ops);
				assert(store);

				Ir &arr = ops.add();
				arr.type = IrType::ARRAY;
				arr.dest = dest;
				arr.regs[0] = store;
				arr.regCount = 1;

				storedIn = dest;
			}
			else {
				for (auto child : tree->children) {
					compile(regNone, child, ops);
				}
			}

			break;
		}
		case AstType::INT_LITERAL: {
			if (dest) {
				storedIn = literal(leaf->number);
			}
			break;
		}
		case AstType::ASSIGN: {
			if (tree->children[0]->type == AstType::LOCAL_VAR) {
				AstLeafNode *local = static_cast<AstLeafNode *>(tree->children[0]);
				assert(local->localIdent->flags & AST_VAR_HAS_REGISTER_ASSIGNED);

				Reg request = reg(local->localIdent->unumber);

				Reg store = compile(request, tree->children[1], ops);
				assert(store);

				if (store != request) {
					Ir &move = ops.add();
					move.type = IrType::SET;
					move.dest = request;
					move.regs[0] = store;
					move.regCount = 1;
				}

				storedIn = store;
			}
			else {
				assert(tree->children[0]->type == AstType::DEREF);

				AstTreeNode *deref = static_cast<AstTreeNode *>(tree->children[0]);

				Reg storeA = compile(reg(nextRegister++), deref->children[0], ops);
				assert(storeA);

				Reg storeB = compile(reg(nextRegister++), tree->children[1], ops);
				assert(storeB);

				Ir &write = ops.add();
				write.type = IrType::WRITE;
				write.regs[0] = storeA;
				write.regs[1] = storeB;
				write.regCount = 2;

				storedIn = storeB;
			}


			break;
		}

		default:
			assert(false);
	}

	return storedIn;
}

static bool canonBinary(Ir *op) {
	if (op->regs[1].type == RegType::REGISTER &&
		((op->regs[0].type == RegType::STATIC_ADROF || op->regs[0].type == RegType::IMMEDIATE) ||
		(op->regs[0].type == RegType::REGISTER && op->regs[0].unumber > op->regs[1].unumber))) {
		std::swap(op->regs[0], op->regs[1]);
		return true;
	}
	else if (op->regs[1].type == RegType::STATIC_ADROF && op->regs[0].type == RegType::IMMEDIATE) {
		std::swap(op->regs[0], op->regs[1]);
		return true;
	}

	return false;
}

static bool canonizeOp(Ir *op) {
	switch (op->type) {
		case IrType::NOOP:
		case IrType::IF_Z:
		case IrType::IF_NZ:
		case IrType::GOTO:
		case IrType::NOT:
		case IrType::SUB:
		case IrType::NEG:
		case IrType::DIV:
		case IrType::MOD:
		case IrType::LSHIFT:
		case IrType::RSHIFT:
		case IrType::ARSHIFT:
		case IrType::ARRAY:
		case IrType::SET:
		case IrType::RETURN:
		case IrType::CALL:
		case IrType::READ:
		case IrType::WRITE:
			return false;
		case IrType::IF_EQ:
		case IrType::IF_NEQ:
		case IrType::IF_AND_Z:
		case IrType::IF_AND_NZ:
		case IrType::AND:
		case IrType::OR:
		case IrType::XOR:
		case IrType::EQ:
		case IrType::NOT_EQ:
		case IrType::MUL:
		case IrType::ADD:
			return canonBinary(op);
		case IrType::IF_L:
			if (canonBinary(op)) {
				op->type = IrType::IF_G;
				return true;
			}

			return false;
		case IrType::IF_LE:
			if (canonBinary(op)) {
				op->type = IrType::IF_GE;
				return true;
			}

			return false;
		case IrType::IF_G:
			if (canonBinary(op)) {
				op->type = IrType::IF_L;
				return true;
			}

			return false;
		case IrType::IF_GE:
			if (canonBinary(op)) {
				op->type = IrType::IF_LE;
				return true;
			}

			return false;
		case IrType::IF_A:
			if (canonBinary(op)) {
				op->type = IrType::IF_B;
				return true;
			}

			return false;
		case IrType::IF_AE:
			if (canonBinary(op)) {
				op->type = IrType::IF_BE;
				return true;
			}

			return false;
		case IrType::IF_B:
			if (canonBinary(op)) {
				op->type = IrType::IF_A;
				return true;
			}

			return false;
		case IrType::IF_BE:
			if (canonBinary(op)) {
				op->type = IrType::IF_AE;
				return true;
			}

			return false;
		case IrType::ABOVE:
			if (canonBinary(op)) {
				op->type = IrType::BELOW;
				return true;
			}

			return false;
		case IrType::ABOVE_EQUAL:
			if (canonBinary(op)) {
				op->type = IrType::BELOW_EQUAL;
				return true;
			}

			return false;
		case IrType::BELOW:
			if (canonBinary(op)) {
				op->type = IrType::ABOVE;
				return true;
			}

			return false;
		case IrType::BELOW_EQUAL:
			if (canonBinary(op)) {
				op->type = IrType::ABOVE_EQUAL;
				return true;
			}

			return false;
		case IrType::GREATER:
			if (canonBinary(op)) {
				op->type = IrType::LESS;
				return true;
			}

			return false;
		case IrType::GREATER_EQUAL:
			if (canonBinary(op)) {
				op->type = IrType::LESS_EQUAL;
				return true;
			}

			return false;
		case IrType::LESS:
			if (canonBinary(op)) {
				op->type = IrType::GREATER;
				return true;
			}

			return false;
		case IrType::LESS_EQUAL:
			if (canonBinary(op)) {
				op->type = IrType::GREATER_EQUAL;
				return true;
			}

			return false;
		default:
			assert(false);
			return false;
	}
}

static bool canonize(DeclFunction *function) {
	PROFILE_FUNC();

	bool change = false;

	for (Ir &op : function->ops) {
		change |= canonizeOp(&op);
	}

	return change;
}


// Basic function to fix up the skipped register numbers when we first generate code so unoptimized builds don't need unusable amounts of stack space
static void reduceRegisterNumbers(DeclFunction *function, ArraySet<ulang> &registersUsed, ulang argCount) {
	PROFILE_FUNC();

	function->largestReg = argCount ? argCount - 1 : 0;

	registersUsed.clear();

	for (Ir &op : function->ops) {
		if (op.dest && op.dest.unumber >= argCount) {
			op.dest.unumber = static_cast<ulang>(registersUsed.addAndGetIndex(op.dest.unumber)) + argCount;
			function->largestReg = my_max(function->largestReg, op.dest.unumber);
		}

		if (op.type == IrType::CALL) {
			for (Reg &reg : op.callRegs) {
				if (reg.type == RegType::REGISTER && reg.unumber >= argCount) {
					reg.unumber = static_cast<ulang>(registersUsed.addAndGetIndex(reg.unumber)) + argCount;
					function->largestReg = my_max(function->largestReg, reg.unumber);
				}
			}
		}
		else {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.regs[i].type == RegType::REGISTER && op.regs[i].unumber >= argCount) {
					op.regs[i].unumber = static_cast<ulang>(registersUsed.addAndGetIndex(op.regs[i].unumber)) + argCount;
					function->largestReg = my_max(function->largestReg, op.regs[i].unumber);
				}
			}
		}
	}
}

static bool isCompare(IrType type) {
	switch (type) {
		case IrType::EQ:
		case IrType::NOT_EQ:
		case IrType::GREATER:
		case IrType::LESS_EQUAL:
		case IrType::LESS:
		case IrType::GREATER_EQUAL:
		case IrType::ABOVE:
		case IrType::BELOW_EQUAL:
		case IrType::BELOW:
		case IrType::ABOVE_EQUAL:
			return true;
		default:
			return false;
	}
}

static bool isConditionalBranch(IrType type) {
	return type >= IrType::IF_Z && type <= IrType::IF_AND_NZ;
}

static bool isJump(IrType type) {
	return type >= IrType::IF_Z && type <= IrType::GOTO;
}


static bool continuesToNext(IrType type) {
	return type != IrType::RETURN && type != IrType::GOTO;
}


static s64 findAndFlagLoop(DeclFunction *function, u32 index, u64 visited, u64 loop) {
	Ir &op = function->ops[index];
	if (!(visited & (1ULL << index))) {

		visited |= 1ULL << index;
		loop |= 1ULL << index;

		if (continuesToNext(op.type) && index + 1 < function->ops.size()) {
			s64 found = findAndFlagLoop(function, index + 1, visited, loop);

			if (found != -1) {
				if (found == -2 || found == index) {
					return -2;
				}

				op.flags |= IR_IS_IN_LOOP;

				return found;
			}
		}


		if (isJump(op.type) && op.jumpTarget < function->ops.size()) {
			s64 found = findAndFlagLoop(function, op.jumpTarget, visited, loop);

			if (found != -1) {
				if (found == -2 || found == index) {
					return -2;
				}

				op.flags |= IR_IS_IN_LOOP;

				return found;
			}
		}

		loop &= ~(1ULL << index);

		return -1;
	}
	else {
		if (loop & (1ULL << index)) {
			op.flags |= IR_IS_IN_LOOP;
			return index;
		}

		return -1;
	}
}

static constexpr u64 BIT_COUNT_IN_U64 = sizeof(u64) * CHAR_BIT;

static s64 findAndFlagLoopSlow(DeclFunction *function, u32 index, u64 *visited, u64 *loop) {
	Ir &op = function->ops[index];
	if (!(visited[index / BIT_COUNT_IN_U64] & (1ULL << (index % BIT_COUNT_IN_U64)))) {

		visited[index / BIT_COUNT_IN_U64] |= 1ULL << (index % BIT_COUNT_IN_U64);
		loop[index / BIT_COUNT_IN_U64] |= 1ULL << (index % BIT_COUNT_IN_U64);


		if (continuesToNext(op.type) && index + 1 < function->ops.size()) {
			s64 found = findAndFlagLoopSlow(function, index + 1, visited, loop);

			if (found != -1) {
				if (found == -2 || found == index) {
					return -2;
				}

				op.flags |= IR_IS_IN_LOOP;

				return found;
			}
		}


		if (isJump(op.type) && op.jumpTarget < function->ops.size()) {
			s64 found = findAndFlagLoopSlow(function, op.jumpTarget, visited, loop);


			if (found != -1) {
				if (found == -2 || found == index) {
					return -2;
				}

				op.flags |= IR_IS_IN_LOOP;

				return found;
			}
		}

		loop[index / BIT_COUNT_IN_U64] &= ~(1ULL << (index % BIT_COUNT_IN_U64));

		return -1;
	}
	else {
		if (loop[index / BIT_COUNT_IN_U64] & (1ULL << (index % BIT_COUNT_IN_U64))) {
			op.flags |= IR_IS_IN_LOOP;
			return index;
		}

		return -1;
	}
}

static void findLoops(DeclFunction *function) {
	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &leader = function->ops[i];

		if (leader.flags & IR_IS_LEADER && !(leader.flags & IR_IS_IN_LOOP)) {
			findAndFlagLoop(function, i, 0, 0);
		}
	}
}

static void findLoopsSlow(DeclFunction *function) {
	u64 size = (function->ops.size() + BIT_COUNT_IN_U64 - 1) / BIT_COUNT_IN_U64 * sizeof(u64);

	u64 *visited = static_cast<u64 *>(alloca(size));
	u64 *loop = static_cast<u64 *>(alloca(size));

	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &leader = function->ops[i];

		if (leader.flags & IR_IS_LEADER && !(leader.flags & IR_IS_IN_LOOP)) {
			memset(visited, 0, size);
			findAndFlagLoopSlow(function, i, visited, loop);
		}
	}
}

void calculateInLoop(DeclFunction *function) {
	PROFILE_FUNC();

	if (!function->ops.size()) return;

	if (function->ops.size() >= BIT_COUNT_IN_U64) {
		findLoopsSlow(function);
	}
	else {
		findLoops(function);
	}

}

void calculateLeaders(DeclFunction *function) {
	PROFILE_FUNC();

	if (!function->ops.size()) return;

	for (auto &op : function->ops) {
		op.flags = 0;
	}

	function->ops[0].flags |= IR_IS_LEADER;
	function->ops[0].flags |= IR_IS_JUMP_TARGET;

	for (u32 i = 0 /* We still have to start at 0 since it could be a jump that could make something else a leader */; i < function->ops.size(); i++) {
		if (isConditionalBranch(function->ops[i].type)) {
			if (i + 1 < function->ops.size()) {
				function->ops[i + 1].flags |= IR_IS_LEADER;
			}

			if (function->ops[i].jumpTarget < function->ops.size()) {
				if (function->ops[function->ops[i].jumpTarget].flags & IR_IS_JUMP_TARGET) {
					function->ops[function->ops[i].jumpTarget].flags |= IR_IS_LEADER | IR_IS_MULTIPLE_JUMP_TARGET;
				}
				function->ops[function->ops[i].jumpTarget].flags |= IR_IS_LEADER | IR_IS_JUMP_TARGET;
			}
		}
		else if (function->ops[i].type == IrType::GOTO) {
			if (function->ops[i].jumpTarget < function->ops.size()) {
				if (function->ops[function->ops[i].jumpTarget].flags & IR_IS_JUMP_TARGET) {
					function->ops[function->ops[i].jumpTarget].flags |= IR_IS_LEADER | IR_IS_MULTIPLE_JUMP_TARGET;
				}
				function->ops[function->ops[i].jumpTarget].flags |= IR_IS_LEADER | IR_IS_JUMP_TARGET;
			}
		}
	}
}

IrType getOpposite(IrType a) {
	switch (a) {
		case IrType::IF_Z:
			return IrType::IF_NZ;
		case IrType::IF_NZ:
			return IrType::IF_Z;
		case IrType::IF_EQ:
			return IrType::IF_NEQ;
		case IrType::IF_NEQ:
			return IrType::IF_EQ;
		case IrType::IF_G:
			return IrType::IF_LE;
		case IrType::IF_LE:
			return IrType::IF_G;
		case IrType::IF_L:
			return IrType::IF_GE;
		case IrType::IF_GE:
			return IrType::IF_L;
		case IrType::IF_A:
			return IrType::IF_BE;
		case IrType::IF_BE:
			return IrType::IF_A;
		case IrType::IF_B:
			return IrType::IF_AE;
		case IrType::IF_AE:
			return IrType::IF_B;
		case IrType::IF_AND_Z:
			return IrType::IF_AND_NZ;
		case IrType::IF_AND_NZ:
			return IrType::IF_AND_Z;
		default:
			assert(false);
			return IrType::INVALID;
	}

}

bool isOppositeBranch(IrType a, IrType b) {
	return isConditionalBranch(b) && a == getOpposite(b);
}

static bool basicThreadJumps(DeclFunction *function) {
	PROFILE_FUNC();

	auto &ops = function->ops;

	bool change = false;

	for (u32 i = 0; i < ops.size(); i++) {
		Ir &op = ops[i];

		if (op.type == IrType::GOTO) {

			if (op.jumpTarget == i + 1) {
				changeToNoop(op);
				change = true;
			}
			else if (op.jumpTarget < ops.size()) {

				Ir *target = &ops[op.jumpTarget];

				if (target->type == IrType::GOTO) {
					op.jumpTarget = target->jumpTarget;
					change = true;
				}
			}
		}
		else if (isConditionalBranch(op.type)) {
			if (op.jumpTarget == i + 1) {
				changeToNoop(op);
				change = true;
			}
			else if (op.type == IrType::IF_Z && op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number != 0) {
				changeToNoop(op);
				change = true;
			}
			else if (op.type == IrType::IF_Z && op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == 0) {
				op.type = IrType::GOTO;
				op.regCount = 0;
				change = true;
			}
			else if (op.type == IrType::IF_NZ && op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number != 0) {
				op.type = IrType::GOTO;
				op.regCount = 0;
				change = true;
			}
			else if (op.type == IrType::IF_NZ && op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == 0) {
				changeToNoop(op);
				change = true;

			}
			else if (op.jumpTarget < ops.size()) {
				Ir *target = &ops[op.jumpTarget];

				if (target->type == IrType::GOTO ||
					(target->type == op.type &&
						target->regs[0] == op.regs[0] &&
						(op.regCount == 1 || target->regs[1] == op.regs[1]))) {
					change = op.jumpTarget != target->jumpTarget;
					op.jumpTarget = target->jumpTarget;
				}
				else if (isOppositeBranch(op.type, target->type) &&
					target->regs[0] == op.regs[0] &&
					(op.regCount == 1 || target->regs[1] == op.regs[1])) {
					op.jumpTarget++;
					change = true;
				}
				else if (i + 2 < ops.size()) {
					Ir *next = &ops[i] + 1;

					if (i + 2 < ops.size() && op.jumpTarget == i + 2 && !(next->flags & IR_IS_JUMP_TARGET) && (next->type == IrType::GOTO ||
						(isOppositeBranch(op.type, next->type) &&
							next->regs[0] == op.regs[0] &&
							(op.regCount == 1 || next->regs[1] == op.regs[1])))) {

						next->regCount = op.regCount;
						for (ulang j = 0; j < op.regCount; j++) {
							next->regs[j] = op.regs[j];
						}
						next->type = getOpposite(op.type);

						changeToNoop(op);

						change = true;
					}
				}
			}
		}
	}

	return change;
}

static bool deleteUnreachable(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	bool isInBlock = true;

	for (auto &op : function->ops) {
		if (op.flags & IR_IS_LEADER) {
			isInBlock = true;
		}

		if (!isInBlock && op.type != IrType::NOOP) {
			changeToNoop(op);

			change = true;
		}

		if (!continuesToNext(op.type))
			isInBlock = false;
	}

	return change;
}


static bool doesReturn(Array<Ir> &ops) {
	if (!ops.size()) return false;

	for (auto &op : ops) {
		if (isJump(op.type) && op.jumpTarget >= ops.size()) {
			return false;
		}
	}

	Ir &last = ops[ops.size() - 1];

	return last.type == IrType::RETURN || last.type == IrType::GOTO; // We wil have already returned false if this goto just jumps directly forward off the end of the function
}

static void makeReturn(Array<Ir> &ops) {
	if (!doesReturn(ops)) {
		Ir &ret = ops.add();
		ret.type = IrType::RETURN;
	}
}

static bool removeNoops(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	for (u32 i = 0; i < function->ops.size(); i++) {
		if (function->ops[i].type == IrType::NOOP) {
			if (i + 1 < function->ops.size()) {
				function->ops[i + 1].flags |= function->ops[i].flags & (IR_IS_LEADER | IR_IS_JUMP_TARGET | IR_IS_MULTIPLE_JUMP_TARGET | IR_IS_IN_LOOP);
			}

			for (u32 j = 0; j < function->ops.size(); j++) {
				if (function->ops[j].jumpTarget > i) {
					--function->ops[j].jumpTarget;
				}

				if (j > i) {
					function->ops[j - 1] = function->ops[j];
				}
			}

			change = true;
			function->ops.pop();
		}
	}

	for (u32 i = 0; i < function->ops.size(); i++) {
		if (function->ops[i].type == IrType::SET && function->ops[i].dest == function->ops[i].regs[0]) {
			changeToNoop(function->ops[i]);
			change = true;
		}
		else if (function->ops[i].jumpTarget > function->ops.size()) {
			function->ops[i].jumpTarget = function->ops.size();
			change = true;
		}
	}

	return change;
}

u64 getU64SForAllRegisters(DeclFunction *function) {
	return function->largestReg / BIT_COUNT_IN_U64 + 1;
}


u64 getRequiredLiveRangeInfoSize(DeclFunction *function) {
	return (function->ops.size() * 2ULL + 2ULL) * getU64SForAllRegisters(function);
}

u64 getRequiredInterferenceGraphSize(DeclFunction *function) {
	return (function->largestReg + 1ULL) * (getU64SForAllRegisters(function) + 6ULL);
}

static void calculateInterferenceGraphSlow(DeclFunction *function, u64 *interferenceBits, u64 *liveRangeBits) {
	PROFILE_FUNC();

	u64 addressCount = getU64SForAllRegisters(function);

	u64 *liveIn = liveRangeBits + 2 * addressCount;
	u64 *liveOut = liveIn + function->ops.size() * addressCount;

	memset(interferenceBits, 0, (function->largestReg + 1ULL) * sizeof(u64) * addressCount);

	for (u64 i = 0; i < function->ops.size(); i++) {

		for (u64 j = 0; j < addressCount; j++) {
			u64 opIn = liveIn[i * addressCount + j];

			for (u64 bits = opIn; bits; bits = _blsr_u64(bits)) {
				unsigned long index;
				BitScanForward64(&index, bits);

				index += static_cast<unsigned long>(BIT_COUNT_IN_U64 * j);

				for (u64 k = 0; k < addressCount; k++) {
					interferenceBits[index * addressCount + k] |= liveIn[i * addressCount + k];
				}
			}
		}

		for (u64 j = 0; j < addressCount; j++) {
			u64 opOut = liveOut[i * addressCount + j];

			for (u64 bits = opOut; bits; bits = _blsr_u64(bits)) {
				unsigned long index;
				BitScanForward64(&index, bits);

				index += static_cast<unsigned long>(BIT_COUNT_IN_U64 * j);

				for (u64 k = 0; k < addressCount; k++) {
					interferenceBits[index * addressCount + k] |= liveOut[i * addressCount + k];
				}
			}
		}
	}
}

static void calculateInterferenceGraph(DeclFunction *function, u64 *interferenceBits, u64 *liveRangeBits) {
	PROFILE_FUNC();

	if (function->largestReg >= BIT_COUNT_IN_U64) {
		calculateInterferenceGraphSlow(function, interferenceBits, liveRangeBits);
	}
	else {
		memset(interferenceBits, 0, (function->largestReg + 1ULL) * sizeof(u64));
		u64 *liveIn = liveRangeBits + 2;
		u64 *liveOut = liveIn + function->ops.size();



		for (u64 i = 0; i < function->ops.size(); i++) {
			u64 opIn = liveIn[i];

			for (u64 bits = opIn; bits; bits = _blsr_u64(bits)) {
				unsigned long idx;
				BitScanForward64(&idx, bits);

				interferenceBits[idx] |= opIn;
			}

			u64 opOut = liveOut[i];
			for (u64 bits = opOut; bits; bits = _blsr_u64(bits)) {
				unsigned long idx;
				BitScanForward64(&idx, bits);

				interferenceBits[idx] |= opOut;
			}
		}
	}
}

// General purpose procedure to calculate the live range bitfields for a subroutine with an arbitrary number of registers
static void calculateLiveRangesSlow(DeclFunction *function, u64 *bits) {
	PROFILE_FUNC();

	u64 addressCount = getU64SForAllRegisters(function);

	u64 *newIn = bits;
	u64 *newOut = newIn + addressCount;
	u64 *liveIn = newOut + addressCount;
	u64 *liveOut = liveIn + function->ops.size() * addressCount;

	memset(liveIn, 0, 2ULL * function->ops.size() * addressCount * sizeof(u64));

	bool change;
	do {
		change = false;

		for (u32 i = 0; i < function->ops.size(); i++) {
			Ir &op = function->ops[i];

			memcpy(newIn, liveOut + i * addressCount, sizeof(u64) * addressCount);
			memset(newOut, 0, sizeof(u64) * addressCount);

			if (op.dest) {
				newIn[op.dest.unumber / BIT_COUNT_IN_U64] &= ~(1ULL << (op.dest.unumber % BIT_COUNT_IN_U64));
			}

			if (op.type == IrType::CALL) {
				for (u32 j = 0; j < op.regCount; j++) {
					if (op.callRegs[j].type == RegType::REGISTER)
						newIn[op.callRegs[j].unumber / BIT_COUNT_IN_U64] |= 1ULL << (op.callRegs[j].unumber % BIT_COUNT_IN_U64);
				}
			}
			else {
				for (u32 j = 0; j < op.regCount; j++) {
					if (op.regs[j].type == RegType::REGISTER)
						newIn[op.regs[j].unumber / BIT_COUNT_IN_U64] |= 1ULL << (op.regs[j].unumber % BIT_COUNT_IN_U64);
				}
			}

			if (memcmp(liveIn + i * addressCount, newIn, sizeof(u64) * addressCount) != 0) {
				change = true;
				memcpy(liveIn + i * addressCount, newIn, sizeof(u64) * addressCount);
			}

			if (op.jumpTarget < function->ops.size() && isJump(op.type)) {
				for (u32 j = 0; j < addressCount; j++) {
					newOut[j] |= liveIn[op.jumpTarget * addressCount + j];
				}
			}

			if (i + 1 < function->ops.size() && continuesToNext(op.type)) {
				for (u32 j = 0; j < addressCount; j++) {
					newOut[j] |= liveIn[(i + 1) * addressCount + j];
				}
			}

			if (memcmp(liveOut + i * addressCount, newOut, sizeof(u64) * addressCount) != 0) {
				change = true;
				memcpy(liveOut + i * addressCount, newOut, sizeof(u64) * addressCount);
			}
		}
	} while (change);

	//for (u64 i = 0; i < function->ops.size(); i++) {
	//	for (u32 j = 0; j < addressCount; j++) {
	//		for (u64 bits = liveIn[i * addressCount + j]; bits; bits = _blsr_u64(bits)) {
	//			unsigned long index;
	//			BitScanForward64(&index, bits);

	//			index += j * BIT_COUNT_IN_U64;

	//			if (index > function->largestReg) {
	//				int a = 0;
	//			}
	//		}

	//		for (u64 bits = liveOut[i * addressCount + j]; bits; bits = _blsr_u64(bits)) {
	//			unsigned long index;
	//			BitScanForward64(&index, bits);

	//			index += j * BIT_COUNT_IN_U64;

	//			if (index > function->largestReg) {
	//				int a = 0;
	//			}
	//		}
	//	}
	//}
}

void calculateLiveRanges(DeclFunction *function, u64 *bits) {
	PROFILE_FUNC();

	if (function->largestReg >= BIT_COUNT_IN_U64) {
		calculateLiveRangesSlow(function, bits);
	}
	else {
		// Special purpose procedure to calculate the live range bitfields for a subroutine with an < 64 registers much faster than the general method

		u64 *liveIn = bits + 2;
		u64 *liveOut = liveIn + function->ops.size();

		memset(liveIn, 0, 2ULL * function->ops.size() * sizeof(u64));

		bool change;

		do {
			change = false;

			for (u32 i = 0; i < function->ops.size(); i++) {
				Ir &op = function->ops[i];

				u64 newIn = liveOut[i];
				u64 newOut = 0;


				if (op.dest)
					newIn &= ~(1ULL << op.dest.unumber);

				if (op.type == IrType::CALL) {
					for (u32 j = 0; j < op.regCount; j++) {
						if (op.callRegs[j].type == RegType::REGISTER)
							newIn |= 1ULL << op.callRegs[j].unumber;
					}
				}
				else {
					for (u32 j = 0; j < op.regCount; j++) {
						if (op.regs[j].type == RegType::REGISTER)
							newIn |= 1ULL << op.regs[j].unumber;
					}
				}

				if (newIn != liveIn[i]) {
					change = true;
					liveIn[i] = newIn;
				}

				if (op.jumpTarget < function->ops.size() && isJump(op.type)) {
					newOut |= liveIn[op.jumpTarget];
				}

				if (i + 1 < function->ops.size() && continuesToNext(op.type)) {
					newOut |= liveIn[i + 1];
				}

				if (newOut != liveOut[i]) {
					change = true;
					liveOut[i] = newOut;
				}
			}
		} while (change);
	}
}

static void doCoalesce(DeclFunction *function, Reg &dest, Reg &src) {
	ulang destNumber = dest.unumber;

	for (Ir &op : function->ops) {
		if (op.dest && op.dest.unumber == destNumber) {
			op.dest.unumber = src.unumber;
		}

		if (op.type == IrType::CALL) {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.callRegs[i].type == RegType::REGISTER && op.callRegs[i].unumber == destNumber) {
					op.callRegs[i].unumber = src.unumber;
				}
			}
		}
		else {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.regs[i].type == RegType::REGISTER && op.regs[i].unumber == destNumber) {
					op.regs[i].unumber = src.unumber;
				}
			}
		}
	}
}

static bool tryCoalesceSlow(DeclFunction *function, Reg &dest, Reg &src, u64 *interferenceBits) {
	u64 addressCount = getU64SForAllRegisters(function);

	if (interferenceBits[dest.unumber * addressCount + src.unumber / BIT_COUNT_IN_U64] & (1ULL << (src.unumber % BIT_COUNT_IN_U64))) return false;

	for (u64 i = 0; i < addressCount; i++) {
		for (u64 bits = interferenceBits[dest.unumber * addressCount + i]; bits; bits = _blsr_u64(bits)) {
			unsigned long inter;
			BitScanForward64(&inter, bits);

			inter += static_cast<unsigned long>(i * BIT_COUNT_IN_U64);

			interferenceBits[inter * addressCount + src.unumber / BIT_COUNT_IN_U64] |= (1ULL << (src.unumber % BIT_COUNT_IN_U64));
			interferenceBits[inter * addressCount + dest.unumber / BIT_COUNT_IN_U64] &= ~(1ULL << (dest.unumber % BIT_COUNT_IN_U64));
		}
	}

	for (u64 i = 0; i < addressCount; i++) {
		interferenceBits[src.unumber * addressCount + i] |= interferenceBits[dest.unumber * addressCount + i];
	}

	memset(interferenceBits + dest.unumber * addressCount, 0, sizeof(u64) * addressCount);

	doCoalesce(function, dest, src);

	return true;
}

static bool tryCoalesce(DeclFunction *function, Reg &dest, Reg &src, u64 *interferenceBits) {
	if (dest.type != RegType::REGISTER || src.type != RegType::REGISTER || dest.unumber == src.unumber) return false;

	if (function->largestReg >= BIT_COUNT_IN_U64) {
		return tryCoalesceSlow(function, dest, src, interferenceBits);
	}


	if (interferenceBits[dest.unumber] & (1ULL << src.unumber)) return false;

	for (u64 bits = interferenceBits[dest.unumber]; bits; bits = _blsr_u64(bits)) {
		unsigned long inter;
		BitScanForward64(&inter, bits);

		interferenceBits[inter] |= (1ULL << src.unumber);
		interferenceBits[inter] &= ~(1ULL << dest.unumber);
	}

	interferenceBits[src.unumber] |= interferenceBits[dest.unumber];
	interferenceBits[dest.unumber] = 0;

	doCoalesce(function, dest, src);

	return true;
}

static bool coalesceRegisters(DeclFunction *function, u64 *interferenceBits) {
	PROFILE_FUNC();

	bool change = false;

	for (Ir &op : function->ops) {
		switch (op.type) {
			case IrType::AND:
			case IrType::OR:
			case IrType::XOR:
			case IrType::EQ:
			case IrType::NOT_EQ:
			case IrType::ADD:
			case IrType::SUB:
				change |= tryCoalesce(function, op.dest, op.regs[0], interferenceBits);
				change |= tryCoalesce(function, op.dest, op.regs[1], interferenceBits);
				break;
			case IrType::NEG:
			case IrType::NOT:
			case IrType::SET:
			case IrType::LSHIFT:
			case IrType::RSHIFT:
			case IrType::ARSHIFT:
				change |= tryCoalesce(function, op.dest, op.regs[0], interferenceBits);
				break;
		}
	}

	return change;
}

static void scoreRegisters(DeclFunction *function, u64 *score, u64 *affinities, ulang parameterCount) {
	for (ulang i = 0; i < parameterCount; i++) {
		affinities[i * 4 + i] += 2; // The parameters should try and stay in their calling convention registers if possible
	}

	for (Ir &op : function->ops) {
		u64 inc = 1; // op.flags & IR_IS_IN_LOOP ? 10 : 1; @Incomplete change to this when we have loop detection

		if (op.type == IrType::IF_NZ && op.regs[0].type == RegType::REGISTER) {
			affinities[op.regs[0].unumber * 4 + 2] += inc;
			score[op.regs[0].unumber] += inc;
		}
		else if (op.type == IrType::RETURN && op.regCount == 1 && op.regs[0].type == RegType::REGISTER) {
			affinities[op.regs[0].unumber * 4 + 0] += 1;
			score[op.regs[0].unumber] += inc;
		}
		else if (op.type == IrType::CALL) {
			if (op.dest) {
				affinities[op.dest.unumber * 4 + 0] += 1;
				score[op.dest.unumber] += inc;
			}

			for (u32 i = 1; i < my_min(5, op.callRegs.size()); i++) {
				if (op.callRegs[i].type == RegType::REGISTER) {
					affinities[op.callRegs[i].unumber * 4ULL + (i - 1ULL)] += 2;
					score[op.callRegs[i].unumber] += inc * 2;
				}
			}
		}

		if (op.dest) {
			score[op.dest.unumber] += inc;
		}

		if (op.type == IrType::CALL) {
			for (u32 i = 0; i < op.regCount; i++) {
				if (op.callRegs[i].type == RegType::REGISTER) {
					score[op.callRegs[i].unumber] += inc;
				}
			}
		}
		else {
			for (u32 i = 0; i < op.regCount; i++) {
				if (op.regs[i].type == RegType::REGISTER) {
					score[op.regs[i].unumber] += inc;
				}
			}
		}
	}
}

static void allocateRegistersSlow(DeclFunction *function, ulang parameterCount, u64 *interferenceBits) {
	PROFILE_FUNC();

	u64 addressCount = getU64SForAllRegisters(function);

	u64 *interferences = interferenceBits;
	u64 **interferencesCopy = static_cast<u64 **>(alloca(sizeof(u64 *) * (function->largestReg + 1)));
	u64 *affinities = interferenceBits + (function->largestReg + 1ULL) * addressCount;
	u64 *score = affinities + 4ULL * (function->largestReg + 1ULL);
	u64 *allocatedRegs = score + (function->largestReg + 1ULL);

	memset(affinities, 0, 5ULL * (function->largestReg + 1ULL) * sizeof(u64));

	for (u64 i = 0; i <= function->largestReg; i++) {
		interferencesCopy[i] = interferences + i * addressCount;
	}

	scoreRegisters(function, score, affinities, parameterCount);
	

	ulang *stack = static_cast<ulang *>(malloc((function->largestReg + 1ULL) * sizeof(ulang)));
	u64 index = 0;

	u64 interferencesCopySize = function->largestReg + 1ULL; // @Volatile, relies on the register numbers not having gaps, so reduceRegisterNumbers must have been called first

	while (interferencesCopySize > 0) {
		s64 select = -1;
		u64 weakestAffinity = std::numeric_limits<u64>::max();

		for (s64 i = 0; i <= function->largestReg; i++) {

			if (interferencesCopy[i]) {
				u64 popcnt = 0;

				for (u64 j = 0; j < addressCount; j++) {
					popcnt += __popcnt64(interferencesCopy[i][j]);
				}

				if (popcnt <= 4) {
					u64 affinity = 0;

					for (u32 j = 0; j < 4; j++) {
						affinity += affinities[i * 4 + j];
					}

					if (affinity < weakestAffinity) {
						weakestAffinity = affinity;
						select = i;
					}
				}
			}
		}

		if (select == -1) {
			u64 leastUses = std::numeric_limits<u64>::max();

			for (u64 i = 0; i <= function->largestReg; i++) {
				if (interferencesCopy[i]) {
					if (score[i] < leastUses) {
						leastUses = score[i];
						select = i;
					}
				}
			}
		}

		stack[index++] = static_cast<ulang>(select);

		u64 *interference = interferencesCopy[select];
		interferencesCopy[select] = nullptr;
		--interferencesCopySize;

		for (u64 i = 0; i < addressCount; i++) {
			u64 j = interference[i];

			for (u64 bits = j; bits; bits &= (bits - 1)) {
				unsigned long inter;

				BitScanForward64(&inter, bits);

				inter += static_cast<unsigned long>(BIT_COUNT_IN_U64 * i);

				if (inter != select) {
					u64 *other = interferencesCopy[inter];

					if (other) {
						other[select / BIT_COUNT_IN_U64] &= ~(1ULL << (select % BIT_COUNT_IN_U64));
					}
				}
			}
		}
	}

	memset(allocatedRegs, 0xFF, (function->largestReg + 1ULL) * sizeof(u64));

	function->largestReg = parameterCount ? parameterCount - 1 : 0;

	while (index) {
		ulang reg = stack[--index];

		ulang regs[] = { 0, 1, 2, 3 };

		std::stable_sort(regs, regs + 4, [affinities, reg](ulang a, ulang b) { return affinities[reg * 4 + a] > affinities[reg * 4 + b];  });

		ulang select = 4;

		for (ulang i = 0; i < 4; i++) {
			for (u64 j = 0; j < addressCount; j++) {
				for (u64 bits = interferences[reg * addressCount + j]; bits; bits = _blsr_u64(bits)) {
					unsigned long inter = 0;
					BitScanForward64(&inter, bits);

					inter += static_cast<unsigned long>(j * BIT_COUNT_IN_U64);

					if (allocatedRegs[inter] == regs[i]) {
						goto cont;
					}
				}
			}

			if (reg < parameterCount) { // Parameters may not interfere if they are never used, so check anyway to make sure multiple parameters aren't allocated to the same register
				for (u64 j = 0; j < parameterCount; j++) {
					if (allocatedRegs[j] == regs[i]) {
						goto cont;
					}
				}
			}

			select = regs[i];
			goto done;

		cont:
			continue;
		}
		{
		loop:

			for (u64 j = 0; j < addressCount; j++) {
				for (u64 bits = interferences[reg * addressCount + j]; bits; bits = _blsr_u64(bits)) {
					unsigned long inter = 0;
					BitScanForward64(&inter, bits);

					inter += static_cast<unsigned long>(j * BIT_COUNT_IN_U64);

					if (allocatedRegs[inter] == select) {
						++select;
						goto loop;
					}
				}
			}

			if (reg < parameterCount) { // Parameters may not interfere if they are never used, so check anyway to make sure multiple parameters aren't allocated to the same register
				for (u64 j = 0; j < parameterCount; j++) {
					if (allocatedRegs[j] == select) {
						++select;
						goto loop;
					}
				}
			}
		}

	done:

		function->largestReg = my_max(function->largestReg, select);
		allocatedRegs[reg] = select;
	}

	free(stack);


	function->shuffle = new ulang[parameterCount];
	function->shuffleCount = parameterCount;

	for (ulang i = 0; i < parameterCount; i++) {
		function->shuffle[i] = allocatedRegs[i];
	}

	for (auto &op : function->ops) {
		if (op.dest)
			op.dest.unumber = static_cast<ulang>(allocatedRegs[op.dest.unumber]);

		if (op.type == IrType::CALL) {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.callRegs[i].type == RegType::REGISTER) {
					op.callRegs[i].unumber = static_cast<ulang>(allocatedRegs[op.callRegs[i].unumber]);
				}
			}
		}
		else {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.regs[i].type == RegType::REGISTER) {
					op.regs[i].unumber = static_cast<ulang>(allocatedRegs[op.regs[i].unumber]);
				}
			}
		}
	}
}


static void allocateRegisters(DeclFunction *function, ulang parameterCount, u64 *interferenceBits) {
	PROFILE_FUNC();
	if (function->largestReg >= BIT_COUNT_IN_U64) {
		allocateRegistersSlow(function, parameterCount, interferenceBits);
	}
	else {
		u64 *interferences = interferenceBits;
		u64 **interferencesCopy = static_cast<u64 **>(alloca(sizeof(u64 *) * (function->largestReg + 1)));
		u64 *affinities = interferenceBits + function->largestReg + 1ULL;
		u64 *score = affinities + 4ULL * (function->largestReg + 1ULL);
		u64 *allocatedRegs = score + (function->largestReg + 1ULL);

		memset(affinities, 0, 5ULL * (function->largestReg + 1ULL) * sizeof(u64));

		for (u64 i = 0; i <= function->largestReg; i++) {
			interferencesCopy[i] = interferences + i;
		}


		scoreRegisters(function, score, affinities, parameterCount);

		ulang stack[BIT_COUNT_IN_U64]; // We know that this won't overflow since function->largestReg < 64 so we have < 64 total registers
		u64 index = 0;

		u64 interferencesCopySize = function->largestReg + 1ULL; // @Volatile, relies on the register numbers not having gaps, so reduceRegisterNumbers must have been called first

		while (interferencesCopySize > 0) {
			s64 select = -1;

			u64 weakestAffinity = std::numeric_limits<u64>::max();

			for (s64 i = 0; i <= function->largestReg; i++) {
				if (interferencesCopy[i] && __popcnt64(*interferencesCopy[i]) <= 4) {
					u64 affinity = 0;

					for (u32 j = 0; j < 4; j++) {
						affinity += affinities[i * 4 + j];
					}

					if (affinity < weakestAffinity) {
						select = i;
						weakestAffinity = affinity;
					}
				}
			}

			if (select == -1) {
				u64 leastUses = std::numeric_limits<u64>::max();

				for (u64 i = 0; i <= function->largestReg; i++) {
					if (interferencesCopy[i]) {
						if (score[i] < leastUses) {
							leastUses = score[i];
							select = i;
						}
					}
				}
			}

			stack[index++] = static_cast<ulang>(select);

			u64 *interference = interferencesCopy[select];
			interferencesCopy[select] = nullptr;
			--interferencesCopySize;

			for (u64 bits = *interference; bits; bits &= (bits - 1)) {
				unsigned long inter;

				BitScanForward64(&inter, bits);

				if (inter != select) {
					u64 *other = interferencesCopy[inter];

					if (other) {
						*other &= ~(1ULL << select);
					}
				}
			}
		}

		memset(allocatedRegs, 0xFF, (function->largestReg + 1ULL) * sizeof(u64));

		function->largestReg = parameterCount ? parameterCount - 1 : 0;

		while (index) {
			ulang reg = stack[--index];

			ulang regs[] = { 0, 1, 2, 3 };

			std::stable_sort(regs, regs + 4, [affinities, reg](ulang a, ulang b) { return affinities[reg * 4 + a] > affinities[reg * 4 + b];  });

			ulang select = 4;

			for (ulang i = 0; i < 4; i++) {
				for (u64 bits = interferences[reg]; bits; bits = _blsr_u64(bits)) {
					unsigned long inter = 0;
					BitScanForward64(&inter, bits);

					if (allocatedRegs[inter] == regs[i]) {
						goto cont;
					}
				}

				if (reg < parameterCount) { // Parameters may not interfere if they are never used, so check anyway to make sure multiple parameters aren't allocated to the same register
					for (u64 j = 0; j < parameterCount; j++) {
						if (allocatedRegs[j] == regs[i]) {
							goto cont;
						}
					}
				}

				select = regs[i];
				goto done;

			cont:
				continue;
			}
			{
			loop:

				for (u64 bits = interferences[reg]; bits; bits = _blsr_u64(bits)) {
					unsigned long inter = 0;
					BitScanForward64(&inter, bits);

					if (allocatedRegs[inter] == select) {
						++select;
						goto loop;
					}
				}

				if (reg < parameterCount) { // Parameters may not interfere if they are never used, so check anyway to make sure multiple parameters aren't allocated to the same register
					for (u64 j = 0; j < parameterCount; j++) {
						if (allocatedRegs[j] == select) {
							++select;
							goto loop;
						}
					}
				}
			}

		done:

			function->largestReg = my_max(function->largestReg, select);
			allocatedRegs[reg] = select;
		}

		function->shuffle = new ulang[parameterCount];
		function->shuffleCount = parameterCount;

		for (ulang i = 0; i < parameterCount; i++) {
			function->shuffle[i] = allocatedRegs[i];
		}

		for (auto &op : function->ops) {
			if (op.dest)
				op.dest.unumber = static_cast<ulang>(allocatedRegs[op.dest.unumber]);

			if (op.type == IrType::CALL) {
				for (ulang i = 0; i < op.regCount; i++) {
					if (op.callRegs[i].type == RegType::REGISTER) {
						op.callRegs[i].unumber = static_cast<ulang>(allocatedRegs[op.callRegs[i].unumber]);
					}
				}
			}
			else {
				for (ulang i = 0; i < op.regCount; i++) {
					if (op.regs[i].type == RegType::REGISTER) {
						op.regs[i].unumber = static_cast<ulang>(allocatedRegs[op.regs[i].unumber]);
					}
				}
			}
		}
	}
}

static bool removeNeverUsedSlow(DeclFunction *function) {
	PROFILE_FUNC();

	u64 size = getU64SForAllRegisters(function) * sizeof(u64);
	u64 *used = static_cast<u64 *>(alloca(size));

	memset(used, 0, size);

	for (Ir &op : function->ops) {
		if (op.type == IrType::CALL) {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.callRegs[i].type == RegType::REGISTER) {
					used[op.callRegs[i].unumber / BIT_COUNT_IN_U64] |= 1ULL << (op.callRegs[i].unumber % BIT_COUNT_IN_U64);
				}
			}
		}
		else {
			for (ulang i = 0; i < op.regCount; i++) {
				if (op.regs[i].type == RegType::REGISTER) {
					used[op.regs[i].unumber / BIT_COUNT_IN_U64] |= 1ULL << (op.regs[i].unumber % BIT_COUNT_IN_U64);
				}
			}
		}
	}

	bool change = false;

	for (Ir &op : function->ops) {
		if (op.dest && (~used[op.dest.unumber / BIT_COUNT_IN_U64] & (1ULL << (op.dest.unumber % BIT_COUNT_IN_U64)))) {
			change = true;
			op.dest = regNone;
			if (op.type != IrType::CALL) {
				changeToNoop(op);
			}
		}
	}

	return change;
}

static bool removeNeverUsed(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		if (!op.dest) continue;

		for (u32 j = i + 1; j < function->ops.size(); j++) {
			Ir &use = function->ops[j];

			if (use.type == IrType::CALL) {
				for (Reg &reg : use.callRegs) {
					if (reg == op.dest) goto done;
				}
			}
			else {
				for (ulang reg = 0; reg < use.regCount; reg++) {
					if (use.regs[reg] == op.dest) goto done;
				}
			}

			if (isConditionalBranch(use.type) || !continuesToNext(use.type) || use.flags & IR_IS_LEADER) break;

			if (use.dest == op.dest) {
				op.dest = regNone;
				if (op.type != IrType::CALL) {
					changeToNoop(op);
				}
				change = true;
				break;
			}
		}
	done:;
	}

	if (function->largestReg >= BIT_COUNT_IN_U64) {
		change |= removeNeverUsedSlow(function);
	}
	else {
		u64 used = 0;

		for (Ir &op : function->ops) {
			if (op.type == IrType::CALL) {
				for (ulang i = 0; i < op.regCount; i++) {
					if (op.callRegs[i].type == RegType::REGISTER) {
						used |= 1ULL << op.callRegs[i].unumber;
					}
				}
			}
			else {
				for (ulang i = 0; i < op.regCount; i++) {
					if (op.regs[i].type == RegType::REGISTER) {
						used |= 1ULL << op.regs[i].unumber;
					}
				}
			}
		}

		for (Ir &op : function->ops) {
			if (op.dest && (~used & (1ULL << op.dest.unumber))) {
				change = true;
				op.dest = regNone;
				if (op.type != IrType::CALL) {
					changeToNoop(op);
				}
			}
		}
	}

	return change;
}

static bool simplifyConstantExpressions(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		switch (op.type) {
			case IrType::ADD: {
				if (op.regs[0].type == RegType::STATIC_ADROF && op.regs[1].type == RegType::IMMEDIATE) {
					op.type = IrType::SET;
					op.regCount = 1;
					op.regs[0].number += op.regs[1].number;
					change = true;
				}

				break;
			}
			case IrType::SUB: {
				if (op.regs[0].type == RegType::STATIC_ADROF && op.regs[1].type == RegType::IMMEDIATE) {
					op.type = IrType::SET;
					op.regCount = 1;
					op.regs[0].number -= op.regs[1].number;
					change = true;
				}
				else if (op.regs[0].type == RegType::IMMEDIATE && op.regs[1].type == RegType::STATIC_ADROF) {
					op.type = IrType::NEG;
					op.regCount = 1;
					op.regs[1].number -= op.regs[0].number;
					op.regs[0] = op.regs[1];
					change = true;
				}

				break;
			}
		}

		if (op.type != IrType::CALL && op.regCount != 0) {
			for (u32 j = 0; j < op.regCount; j++) {
				if (op.regs[j].type != RegType::IMMEDIATE) {
					goto skip;
				}
			}

			slang value = 0;

			switch (op.type) {
				case IrType::ADD:
					value = op.regs[0].number + op.regs[1].number;
					break;
				case IrType::SUB:
					value = op.regs[0].number - op.regs[1].number;
					break;
				case IrType::MUL:
					value = op.regs[0].number * op.regs[1].number;
					break;
				case IrType::DIV:
					value = op.regs[0].number / op.regs[1].number;
					break;
				case IrType::MOD:
					value = op.regs[0].number % op.regs[1].number;
					break;
				case IrType::NEG:
					value = -op.regs[0].number;
					break;
				case IrType::AND:
					value = op.regs[0].number & op.regs[1].number;
					break;
				case IrType::OR:
					value = op.regs[0].number | op.regs[1].number;
					break;
				case IrType::XOR:
					value = op.regs[0].number ^ op.regs[1].number;
					break;
				case IrType::NOT:
					value = ~op.regs[0].number;
					break;
				case IrType::LSHIFT:
					value = op.regs[0].number << (op.regs[1].number & 0xF); // @WordSize
					break;
				case IrType::RSHIFT:
					value = static_cast<slang>(op.regs[0].unumber >> (op.regs[1].unumber & 0xF)); // @WordSize
					break;
				case IrType::ARSHIFT:
					value = op.regs[0].number >> (op.regs[1].number & 0xF); // @WordSize
					break;
				case IrType::GREATER:
					value = op.regs[0].number > op.regs[1].number ? 1 : 0;
					break;
				case IrType::LESS_EQUAL:
					value = op.regs[0].number <= op.regs[1].number ? 1 : 0;
					break;
				case IrType::LESS:
					value = op.regs[0].number < op.regs[1].number ? 1 : 0;
					break;
				case IrType::GREATER_EQUAL:
					value = op.regs[0].number >= op.regs[1].number ? 1 : 0;
					break;
				case IrType::ABOVE:
					value = op.regs[0].unumber > op.regs[1].unumber ? 1 : 0;
					break;
				case IrType::BELOW_EQUAL:
					value = op.regs[0].unumber <= op.regs[1].unumber ? 1 : 0;
					break;
				case IrType::BELOW:
					value = op.regs[0].unumber < op.regs[1].unumber ? 1 : 0;
					break;
				case IrType::ABOVE_EQUAL:
					value = op.regs[0].unumber >= op.regs[1].unumber ? 1 : 0;
					break;
				case IrType::EQ:
					value = op.regs[0].number == op.regs[1].number ? 1 : 0;
					break;
				case IrType::NOT_EQ:
					value = op.regs[0].number != op.regs[1].number ? 1 : 0;
					break;
				case IrType::IF_G:
					op.regCount = 0;
					op.type = op.regs[0].number > op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_LE:
					op.regCount = 0;
					op.type = op.regs[0].number <= op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_L:
					op.regCount = 0;
					op.type = op.regs[0].number < op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_GE:
					op.regCount = 0;
					op.type = op.regs[0].number >= op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_A:
					op.regCount = 0;
					op.type = op.regs[0].unumber > op.regs[1].unumber ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_BE:
					op.regCount = 0;
					op.type = op.regs[0].number <= op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_B:
					op.regCount = 0;
					op.type = op.regs[0].number < op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_AE:
					op.regCount = 0;
					op.type = op.regs[0].number >= op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_EQ:
					op.regCount = 0;
					op.type = op.regs[0].number == op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_NEQ:
					op.regCount = 0;
					op.type = op.regs[0].number != op.regs[1].number ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_Z:
					op.regCount = 0;
					op.type = op.regs[0].number == 0 ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_NZ:
					op.regCount = 0;
					op.type = op.regs[0].number != 0 ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_AND_Z:
					op.regCount = 0;
					op.type = (op.regs[0].unumber & op.regs[1].unumber) == 0 ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				case IrType::IF_AND_NZ:
					op.regCount = 0;
					op.type = (op.regs[0].unumber & op.regs[1].unumber) != 0 ? IrType::GOTO : IrType::NOOP;
					change = true;
					goto skip;
				default:
					goto skip;
			}

			op.type = IrType::SET;
			op.regCount = 1;
			op.regs[0].type = RegType::IMMEDIATE;
			op.regs[0].number = value;
			change = true;
		}

	skip:

		switch (op.type) {
			case IrType::ADD: {
				if (op.regs[1].type == RegType::IMMEDIATE && op.regs[1].number == 0) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::MUL;
					op.regs[1].type = RegType::IMMEDIATE;
					op.regs[1].number = 2;
					change = true;
				}
				break;
			}
			case IrType::SUB: {
				if (op.regs[1].type == RegType::IMMEDIATE && op.regs[1].number == 0) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == 0) {
					op.type = IrType::NEG;
					op.regs[0] = op.regs[1];
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == -1) {
					op.type = IrType::NOT;
					op.regs[0] = op.regs[1];
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::MUL: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == 1) {
						op.type = IrType::SET;
						op.regCount = 1;
						change = true;
					}
					else if (number == -1) {
						op.type = IrType::NEG;
						op.regCount = 1;
						change = true;
					}
					else if (number == 0) {
						op.type = IrType::SET;
						op.regs[0] = op.regs[1];
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::DIV: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == 1) {
						op.type = IrType::SET;
						op.regCount = 1;
						change = true;
					}
					else if (number == -1) {
						op.type = IrType::NEG;
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == 0) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::MOD: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == 1 || number == -1) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 0;
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0].type == RegType::IMMEDIATE && op.regs[0].number == 0) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::RSHIFT:
			case IrType::ARSHIFT:
			case IrType::LSHIFT: {
				if (op.regs[1].type == RegType::IMMEDIATE && op.regs[1].number == 0) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::AND: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MAX) {
						op.type = IrType::SET;
						op.regCount = 1;
						change = true;
					}
					else if (number == 0) {
						op.type = IrType::SET;
						op.regs[0] = op.regs[1];
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::OR: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == 0) {
						op.type = IrType::SET;
						op.regCount = 1;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::SET;
						op.regs[0] = op.regs[1];
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::XOR: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == 0) {
						op.type = IrType::SET;
						op.regCount = 1;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::NOT;
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::EQ: {
				if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_EQ: {
				if (op.regs[1].type == RegType::IMMEDIATE && op.regs[1].unumber == 0) {
					op.type = IrType::IF_Z;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::GOTO;
					op.regCount = 0;
					change = true;
				}
				break;
			}
			case IrType::NOT_EQ: {
				if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_NEQ: {
				if (op.regs[1].type == RegType::IMMEDIATE && op.regs[1].unumber == 0) {
					op.type = IrType::IF_NZ;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[0] == op.regs[1]) {
					changeToNoop(op);
					change = true;
				}
				break;
			}
			case IrType::GREATER: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MAX) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 0;
						op.regCount = 1;
						change = true;
					}
					else if (number == SLANG_MIN) {
						op.type = IrType::NOT_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_G: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MAX) {
						changeToNoop(op);
						change = true;
					}
					else if (number == SLANG_MIN) {
						op.type = IrType::IF_NEQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					changeToNoop(op);
					change = true;
				}
				break;
			}
			case IrType::LESS_EQUAL: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MAX) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 1;
						op.regCount = 1;
						change = true;
					}
					else if (number == SLANG_MIN) {
						op.type = IrType::EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_LE: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MAX) {
						op.type = IrType::GOTO;
						op.regCount = 0;
						change = true;
					}
					else if (number == SLANG_MIN) {
						op.type = IrType::IF_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::GOTO;
					op.regCount = 0;
					change = true;
				}
				break;
			}
			case IrType::LESS: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MIN) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 0;
						op.regCount = 1;
						change = true;
					}
					else if (number == SLANG_MAX) {
						op.type = IrType::NOT_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_L: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MIN) {
						changeToNoop(op);
						change = true;
					}
					else if (number == SLANG_MAX) {
						op.type = IrType::IF_NEQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					changeToNoop(op);
					change = true;
				}
				break;
			}
			case IrType::GREATER_EQUAL: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MIN) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 1;
						op.regCount = 1;
						change = true;
					}
					else if (number == SLANG_MAX) {
						op.type = IrType::EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_GE: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					slang number = op.regs[1].number;

					if (number == SLANG_MIN) {
						op.type = IrType::GOTO;
						op.regCount = 0;
						change = true;
					}
					else if (number == SLANG_MAX) {
						op.type = IrType::IF_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::GOTO;
					op.regCount = 0;
					change = true;
				}
				break;
			}
			case IrType::ABOVE: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MAX) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 0;
						op.regCount = 1;
						change = true;
					}
					else if (number == 0) {
						op.type = IrType::NOT_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_A: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MAX) {
						changeToNoop(op);
						change = true;
					}
					else if (number == ULANG_MIN) {
						op.type = IrType::IF_NZ;
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					changeToNoop(op);
					change = true;
				}
				break;
			}
			case IrType::BELOW_EQUAL: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MAX) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 1;
						op.regCount = 1;
						change = true;
					}
					else if (number == ULANG_MIN) {
						op.type = IrType::EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_BE: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MAX) {
						op.type = IrType::GOTO;
						op.regCount = 0;
						change = true;
					}
					else if (number == ULANG_MIN) {
						op.type = IrType::IF_Z;
						op.regCount = 1;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::GOTO;
					op.regCount = 0;
					change = true;
				}
				break;
			}
			case IrType::BELOW: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MIN) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 0;
						op.regCount = 1;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::NOT_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 0;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_B: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MIN) {
						changeToNoop(op);
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::IF_NEQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					changeToNoop(op);
					change = true;
				}
				break;
			}
			case IrType::ABOVE_EQUAL: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MIN) {
						op.type = IrType::SET;
						op.regs[0].type = RegType::IMMEDIATE;
						op.regs[0].number = 1;
						op.regCount = 1;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::SET;
					op.regs[0].type = RegType::IMMEDIATE;
					op.regs[0].number = 1;
					op.regCount = 1;
					change = true;
				}
				break;
			}
			case IrType::IF_AE: {
				if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (number == ULANG_MIN) {
						op.type = IrType::GOTO;
						op.regCount = 0;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::IF_EQ;
						change = true;
					}
				}
				else if (op.regs[0] == op.regs[1]) {
					op.type = IrType::GOTO;
					op.regCount = 0;
					change = true;
				}
				break;
			}
			case IrType::IF_AND_Z: {
				if (op.regs[0] == op.regs[1]) {
					op.type = IrType::IF_Z;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (op.regs[1].number == SLANG_MIN) { // If we are testing the sign bit is zero
						op.type = IrType::IF_GE;
						op.regs[1].number = 0;
						change = true;
					}
					else if (number == 0) {
						op.type = IrType::GOTO;
						op.regCount = 0;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::IF_Z;
						op.regCount = 1;
						change = true;
					}
				}
				break;
			}
			case IrType::IF_AND_NZ: {
				if (op.regs[0] == op.regs[1]) {
					op.type = IrType::IF_NZ;
					op.regCount = 1;
					change = true;
				}
				else if (op.regs[1].type == RegType::IMMEDIATE) {
					ulang number = op.regs[1].unumber;

					if (op.regs[1].number == SLANG_MIN) { // If we are testing the sign bit is one
						op.type = IrType::IF_L;
						op.regs[1].number = 0;
						change = true;
					}
					else if (number == 0) {
						op.type = IrType::NOOP;
						op.regCount = 0;
						change = true;
					}
					else if (number == ULANG_MAX) {
						op.type = IrType::IF_NZ;
						op.regCount = 1;
						change = true;
					}
				}
				break;
			}
		}

		if (i + 1 < function->ops.size()) {
			Ir &next = function->ops[i + 1];

			if (!(next.flags & IR_IS_LEADER)) {
				if (op.type == IrType::ADD && next.type == IrType::ADD) {
					if (op.dest == next.regs[0] && next.dest != op.regs[0]) {
						if (op.regs[1].type == RegType::STATIC_ADROF && next.regs[1].type == RegType::IMMEDIATE) {
							Ir newOp = {};

							newOp.type = IrType::ADD;
							newOp.regCount = 2;
							newOp.dest = next.dest;
							newOp.regs[0] = op.regs[0];
							newOp.regs[1] = op.regs[1];
							newOp.regs[1].number += next.regs[1].number;

							next = op;
							op = newOp;
							change = true;
						}
						else if (op.regs[1].type == RegType::IMMEDIATE && next.regs[1].type == RegType::STATIC_ADROF) {
							Ir newOp = {};

							newOp.type = IrType::ADD;
							newOp.regCount = 2;
							newOp.dest = next.dest;
							newOp.regs[0] = op.regs[0];
							newOp.regs[1] = next.regs[1];
							newOp.regs[1].number += op.regs[1].number;

							next = op;
							op = newOp;
							change = true;
						}
						else if (op.regs[1].type == RegType::IMMEDIATE && next.regs[1].type == RegType::IMMEDIATE) {
							Ir newOp = {};

							newOp.type = IrType::ADD;
							newOp.regCount = 2;
							newOp.dest = next.dest;
							newOp.regs[0] = op.regs[0];
							newOp.regs[1] = op.regs[1];
							newOp.regs[1].number += next.regs[1].number;

							next = op;
							op = newOp;
							change = true;

						}
					}
					else if (op.dest == next.dest && next.regs[0] == op.dest) {
						if (op.regs[1].type == RegType::STATIC_ADROF && next.regs[1].type == RegType::IMMEDIATE) {
							next.regs[0] = op.regs[0];
							op.regs[1].unumber += next.regs[1].unumber;
							next.regs[1] = op.regs[1];

							changeToNoop(op);

							change = true;
						}
						else if (op.regs[1].type == RegType::IMMEDIATE && (next.regs[1].type == RegType::STATIC_ADROF || next.regs[1].type == RegType::IMMEDIATE)) {
							next.regs[0] = op.regs[0];
							next.regs[1].unumber += op.regs[1].unumber;

							changeToNoop(op);

							change = true;
						}
					}
				}
				else if (op.type == IrType::SUB && next.type == IrType::ADD) {
					if (op.dest == next.regs[0] && next.dest != op.regs[0]) {
						if (op.regs[1].type == RegType::IMMEDIATE && (next.regs[1].type == RegType::STATIC_ADROF || next.regs[1].type == RegType::REGISTER)) {
							Ir newOp = {};

							newOp.type = IrType::ADD;
							newOp.regCount = 2;
							newOp.dest = next.dest;
							newOp.regs[0] = op.regs[0];
							newOp.regs[1] = next.regs[1];
							newOp.regs[1].number -= op.regs[1].number;

							next = op;
							op = newOp;
							change = true;
						}
					}
					else if (op.dest == next.dest && next.regs[0] == op.dest) {
						if (op.regs[1].type == RegType::IMMEDIATE && (next.regs[1].type == RegType::IMMEDIATE || next.regs[1].type == RegType::STATIC_ADROF)) {
							next.regs[0] = op.regs[0];
							next.regs[1].unumber -= op.regs[1].unumber;
							
							changeToNoop(op);
							change = true;
						}
					}
				}
			}
		}
	}

	return change;
}

static bool branchWillBeTaken(ulang unumber, Ir &branch) {
	slang number = static_cast<slang>(unumber);

	switch (branch.type) {
		case IrType::IF_Z:
			return unumber == 0;
		case IrType::IF_NZ:
			return unumber != 0;
		case IrType::IF_EQ:
			return unumber == branch.regs[1].unumber;
		case IrType::IF_NEQ:
			return unumber != branch.regs[1].unumber;
		case IrType::IF_G:
			return number > branch.regs[1].number;
		case IrType::IF_LE:
			return number <= branch.regs[1].number;
		case IrType::IF_L:
			return number < branch.regs[1].number;
		case IrType::IF_GE:
			return number >= branch.regs[1].number;
		case IrType::IF_A:
			return unumber > branch.regs[1].unumber;
		case IrType::IF_BE:
			return unumber <= branch.regs[1].unumber;
		case IrType::IF_B:
			return unumber < branch.regs[1].unumber;
		case IrType::IF_AE:
			return unumber >= branch.regs[1].unumber;
		case IrType::IF_AND_Z:
			return (unumber & branch.regs[1].unumber) == 0;
		case IrType::IF_AND_NZ:
			return (unumber & branch.regs[1].unumber) != 0;
	}

	assert(false);
	return false;
}

static bool propagateInBasicBlock(DeclFunction *function, u32 *index) {
	PROFILE_FUNC();
	u32 end = function->ops.size();

	for (u32 i = *index + 1; i < end; i++) {
		if (function->ops[i].flags & IR_IS_JUMP_TARGET) {
			end = i;
			break;
		}
	}

	bool change = false;

	for (u32 propagate = *index; propagate < end; propagate++) {
		Ir &prop = function->ops[propagate];

		switch (prop.type) {
			case IrType::SET: {
				for (u32 i = propagate + 1; i < end; i++) {
					Ir &op = function->ops[i];

					if (op.type == IrType::CALL) {
						for (ulang j = 0; j < op.regCount; j++) {
							if (op.callRegs[j] == prop.dest) {
								op.callRegs[j] = prop.regs[0];
								change = true;
							}
						}
					}
					else {
						for (ulang j = 0; j < op.regCount; j++) {
							if (op.regs[j] == prop.dest) {
								op.regs[j] = prop.regs[0];
								change = true;
							}
						}
					}

					if (isConditionalBranch(op.type) && prop.regs[0].type == RegType::IMMEDIATE) {
						Ir &target = function->ops[op.jumpTarget];

						if (isConditionalBranch(target.type) && target.regs[0] == prop.dest && (target.regCount == 1 || target.regs[1].type == RegType::IMMEDIATE)) {
							if (branchWillBeTaken(prop.regs[0].unumber, target)) {
								++op.jumpTarget;
							}
							else {
								op.jumpTarget = target.jumpTarget;
							}

							change = true;
						}
					}

					if (op.dest == prop.dest) break;
					if (op.dest == prop.regs[0]) break;
				}

				break;
			}
			case IrType::GREATER:
			case IrType::LESS_EQUAL:
			case IrType::LESS:
			case IrType::GREATER_EQUAL:
			case IrType::ABOVE:
			case IrType::BELOW_EQUAL:
			case IrType::BELOW:
			case IrType::ABOVE_EQUAL:
			case IrType::EQ:
			case IrType::NOT_EQ:
			case IrType::AND: {
				for (u32 i = propagate + 1; i < end; i++) {
					Ir &op = function->ops[i];


					if ((op.type == IrType::IF_Z || op.type == IrType::IF_NZ) && op.regs[0] == prop.dest) {
						op.regCount = 2;
						op.regs[0] = prop.regs[0];
						op.regs[1] = prop.regs[1];
						change = true;

						switch (prop.type) {
							case IrType::GREATER:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_G : IrType::IF_LE;
								break;
							case IrType::LESS_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_LE : IrType::IF_G;
								break;
							case IrType::LESS:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_L : IrType::IF_GE;
								break;
							case IrType::GREATER_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_GE : IrType::IF_L;
								break;
							case IrType::ABOVE:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_A : IrType::IF_BE;
								break;
							case IrType::BELOW_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_BE : IrType::IF_A;
								break;
							case IrType::BELOW:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_B : IrType::IF_AE;
								break;
							case IrType::ABOVE_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_AE : IrType::IF_B;
								break;
							case IrType::EQ:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_EQ : IrType::IF_NEQ;
								break;
							case IrType::NOT_EQ:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_NEQ : IrType::IF_EQ;
								break;
							case IrType::AND:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_AND_NZ : IrType::IF_AND_Z;
								break;
						}
					}

					if (op.dest == prop.dest) break;

					if (op.dest) {
						for (ulang j = 0; j < prop.regCount; j++) {
							if (op.dest == prop.regs[j]) {
								goto break_;
							}
						}
					}
				}
			break_:
				break;
			}
			case IrType::IF_G:
			case IrType::IF_LE:
			case IrType::IF_L:
			case IrType::IF_GE:
			case IrType::IF_A:
			case IrType::IF_BE:
			case IrType::IF_B:
			case IrType::IF_AE:
			case IrType::IF_EQ:
			case IrType::IF_NEQ:
			case IrType::IF_Z:
			case IrType::IF_NZ:
			case IrType::IF_AND_Z:
			case IrType::IF_AND_NZ: {
				for (u32 i = propagate + 1; i < end; i++) {
					Ir &op = function->ops[i];

					if (i == prop.jumpTarget)
						break;

					if (prop.type == IrType::IF_NZ) {
						if (op.type == IrType::CALL) {
							for (ulang j = 0; j < op.regCount; j++) {
								if (op.callRegs[j] == prop.regs[0]) {
									op.callRegs[j].type = RegType::IMMEDIATE;
									op.callRegs[j].number = 0;
									change = true;
								}
							}
						}
						else {
							for (ulang j = 0; j < op.regCount; j++) {
								if (op.regs[j] == prop.regs[0]) {
									op.regs[j].type = RegType::IMMEDIATE;
									op.regs[j].number = 0;
									change = true;
								}
							}
						}
					}

					if (op.type == prop.type) {
						for (ulang j = 0; j < prop.regCount; j++) {
							if (op.regs[j] != prop.regs[j]) {
								goto cont;
							}
						}

						changeToNoop(op);
					}
					else if (op.type == getOpposite(prop.type)) {
						if (op.type == prop.type) {
							for (ulang j = 0; j < prop.regCount; j++) {
								if (op.regs[j] != prop.regs[j]) {
									goto cont;
								}
							}

							op.type = IrType::GOTO;
							op.regCount = 0;
						}
					}

				cont:
					if (op.dest) {
						for (ulang j = 0; j < prop.regCount; j++) {
							if (op.dest == prop.regs[j]) {
								if ((prop.type == IrType::IF_Z || prop.type == IrType::IF_NZ) && op.type == IrType::NEG && op.regs[0] == op.dest) {
									// Negating our self has no effect on if we are zero
								}
								else {
									goto break2_;
								}
							}
						}
					}
				}
			break2_:
				break;
			}
		}
	}

	*index = end;
	return change;
}

static bool removeCommonExpressionsInBasicBlock(DeclFunction *function, u32 *index) {
	PROFILE_FUNC();
	u32 end = function->ops.size();

	for (u32 i = *index + 1; i < end; i++) {
		if (function->ops[i].flags & IR_IS_JUMP_TARGET) {
			end = i;
			break;
		}
	}

	bool change = false;

	for (u32 expression = *index; expression < end; expression++) {
		Ir &expr = function->ops[expression];

		if (expr.dest && expr.type != IrType::READ && expr.type != IrType::WRITE && expr.type != IrType::CALL && expr.type != IrType::SET) {
			for (u32 i = expression + 1; i < end; i++) {
				Ir &op = function->ops[i];

				if (op.type == expr.type) {
					for (u32 reg = 0; reg < op.regCount; reg++) {
						if (op.regs[reg] != expr.regs[reg]) {
							goto skip;
						}
					}

					op.type = IrType::SET;
					op.regCount = 1;
					op.regs[0] = expr.dest;

					change = true;

				skip:;
				}

				if (op.dest == expr.dest) break;

				for (u32 reg = 0; reg < expr.regCount; reg++) {
					if (op.dest == expr.regs[reg]) {
						goto break_;
					}
				}
			}
		}
	break_:;
	}

	*index = end;
	return change;
}

static bool propagateInBasicBlocks(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	u32 index = 0;

	while (index != function->ops.size()) {
		change |= propagateInBasicBlock(function, &index);
	}

	return change;
}

static bool removeCommonExpressions(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	u32 index = 0;

	while (index != function->ops.size()) {
		change |= removeCommonExpressionsInBasicBlock(function, &index);
	}

	return change;
}

constexpr u32 CANT_FIND_USAGE_SENTINEL = 0xFFFFFFFF;

static bool usagesInSameTree(Array<u32> &usages, u32 a, u32 b) {
	for (u32 i = a; i != CANT_FIND_USAGE_SENTINEL; i = usages[i]) {
		for (u32 j = b; j != CANT_FIND_USAGE_SENTINEL; j = usages[j]) {
			if (i == j) return true;
		}
	}

	return false;
}

static bool moveOverwritePastUse(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		Ir &set = function->ops[i];
		Ir overwrite = function->ops[i + 1];

		if (set.type != IrType::SET || (overwrite.flags & IR_IS_LEADER) || set.regs[0] != overwrite.dest) continue;
		
		u32 lastUsage = i + 1;


		for (u32 usage = i + 2; usage < function->ops.size(); usage++) {
			Ir &use = function->ops[usage];

			if (use.type == IrType::CALL) {
				for (Reg &reg : use.callRegs) {
					if (reg == overwrite.dest) {
						goto done;
					}
					else if (reg == set.dest) {
						lastUsage = usage;
					}
				}
			}
			else {
				for (u32 reg = 0; reg < use.regCount; reg++) {
					if (use.regs[reg] == overwrite.dest) {
						goto done;
					}
					else if (use.regs[reg] == set.dest) {
						lastUsage = usage;
					}
				}
			}

			if (use.dest) {
				if (overwrite.type == IrType::CALL) {
					for (Reg &reg : overwrite.callRegs) {
						if (reg == use.dest) {
							goto done;
						}
					}
				}
				else {
					for (u32 reg = 0; reg < overwrite.regCount; reg++) {
						if (overwrite.regs[reg] == use.dest) {
							goto done;
						}
					}
				}
			}


			if (use.dest == overwrite.dest || !continuesToNext(use.type) || isConditionalBranch(use.type) || (use.flags & IR_IS_LEADER)) {
				break;
			}

			if (use.type == IrType::CALL || use.type == IrType::WRITE) {
				if (overwrite.type == IrType::READ || overwrite.type == IrType::WRITE || overwrite.type == IrType::CALL) {
					break;
				}
			}
			else if (use.type == IrType::READ) {
				if (overwrite.type == IrType::WRITE || overwrite.type == IrType::CALL) {
					break;
				}
			}
		}

	done:;

		for (u32 j = i + 1; j < lastUsage; j++) {
			std::swap(function->ops[j], function->ops[j + 1]);
			change = true;
		}
	}

	return change;
}

static u32 isExitBlock(DeclFunction *function, u32 index) {
	u32 size = 0;

	for (u32 i = index; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];
		++size;

		if (op.type == IrType::RETURN) return size;
		if (op.type == IrType::GOTO || isConditionalBranch(op.type)) return 0;
	}

	return size;
}

static u32 isRelocatable(DeclFunction *function, u32 index) {
	u32 size = 0;

	for (u32 i = index; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];
		++size;

		if (isConditionalBranch(op.type)) return 0;


		if (op.type == IrType::RETURN || op.type == IrType::GOTO) return size;
	}

	return size;
}



bool operator==(const Ir &reloc, const Ir &dup) {
	if (reloc.type != dup.type) return false;
	if (reloc.dest != dup.dest) return false;

	if (reloc.type == IrType::CALL) {
		if (reloc.regCount != dup.regCount) return false;

		for (u32 reg = 0; reg < reloc.regCount; reg++) {
			if (reloc.callRegs[reg] != dup.callRegs[reg]) return false;
		}
	}
	else {
		if (isConditionalBranch(reloc.type) || reloc.type == IrType::GOTO) {
			if (reloc.jumpTarget != dup.jumpTarget) return false;
		}

		for (u32 reg = 0; reg < reloc.regCount; reg++) {
			if (reloc.regs[reg] != dup.regs[reg]) return false;
		}
	}

	return true;
}

bool operator!=(const Ir &reloc, const Ir &dup) {
	return !(operator==(reloc, dup));
}

static bool moveDuplicateOutOfBranch(DeclFunction *function) {
	bool change = false;

	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		Ir &branch = function->ops[i];

		if (isConditionalBranch(branch.type)) {
			Ir &next = function->ops[i + 1];
			Ir &target = function->ops[branch.jumpTarget];

			if (next != target) continue;

			if (next.dest == branch.regs[0] || (branch.regCount == 2 && next.dest == branch.regs[1])) continue;

			++branch.jumpTarget;
			std::swap(branch, next);

			change = true;
		}
	}

	return change;
}

static bool moveDuplicateOutOfBranchSlow(DeclFunction *function) {
	bool change = false;

	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		Ir &branch = function->ops[i];

		if (isConditionalBranch(branch.type)) {
			for (u32 next = i + 1; next + 1 < function->ops.size(); next++) {
				Ir &a = function->ops[next];

				if (isConditionalBranch(a.type) || !continuesToNext(a.type)) break;
				if (a.type == IrType::READ || a.type == IrType::WRITE || a.type == IrType::CALL) continue;

				if (a.flags & IR_IS_JUMP_TARGET) break;

				if (a.dest == branch.regs[0] || (branch.regCount == 2 && a.dest == branch.regs[1])) continue;

				for (u32 j = i + 1; j < next; j++) {
					Ir &depend = function->ops[j];

					if (depend.dest == a.dest) goto continue_;

					if (depend.type == IrType::CALL) {
						for (Reg &reg : depend.callRegs) {
							if (reg == a.dest) goto continue_;
						}
					}
					else {
						for (u32 reg = 0; reg < depend.regCount; reg++) {
							if (depend.regs[reg] == a.dest) goto continue_;
						}
					}

					for (u32 reg = 0; reg < a.regCount; reg++) {
						if (a.regs[reg] == depend.dest) goto continue_;
					}
				}

				for (u32 target = branch.jumpTarget; target + 1 < function->ops.size(); target++) {
					if (next == target) break;
					Ir &b = function->ops[target];

					if (target != branch.jumpTarget && (b.flags & IR_IS_JUMP_TARGET)) break;
					if (b.flags & IR_IS_MULTIPLE_JUMP_TARGET) 
						break;

					if (isConditionalBranch(b.type) || !continuesToNext(b.type)) break;

					if (a != b) continue;

					for (u32 j = branch.jumpTarget; j < target; j++) {
						Ir &depend = function->ops[j];

						if (depend.dest == b.dest) goto continue2_;

						if (depend.type == IrType::CALL) {
							for (Reg &reg : depend.callRegs) {
								if (reg == b.dest) goto continue2_;
							}
						}
						else {
							for (u32 reg = 0; reg < depend.regCount; reg++) {
								if (depend.regs[reg] == b.dest) goto continue2_;
							}
						}

						for (u32 reg = 0; reg < b.regCount; reg++) {
							if (b.regs[reg] == depend.dest) goto continue2_;
						}
					}

					u32 t = ++branch.jumpTarget;

					for (u32 j = next; j >= i + 1; j--) {
						std::swap(function->ops[j], function->ops[j - 1]);
					}

					for (u32 j = target; j >= t; j--) {
						std::swap(function->ops[j], function->ops[j - 1]);
					}

					change = true;
					goto done;

				continue2_:;
				}

			continue_:;
			}
		}

	done:;
	}

	return change;
}

static bool deduplicate(DeclFunction *function) {
	PROFILE_FUNC();

	bool change = false;

	for (s32 i = function->ops.size() - 2; i >= 0; i--) {
		Ir &op = function->ops[i];

		if (!continuesToNext(op.type)) {
			u32 exitBlockSize = isRelocatable(function, i + 1);

			if (exitBlockSize) {
				for (s32 j = 0; j < i - (s32) exitBlockSize + 2; j++) {
					for (u32 k = 0; k < exitBlockSize; k++) {
						Ir &reloc = function->ops[i + 1 + k];
						Ir &dup = function->ops[j + k];

						if (reloc != dup) goto skip;
					}
					int aaa = 0;

					for (u32 k = 0; k < function->ops.size(); k++) {
						Ir &branch = function->ops[k];

						if (branch.jumpTarget >= i + 1 && branch.jumpTarget < i + 1 + exitBlockSize) {
							branch.jumpTarget -= i + 1;
							branch.jumpTarget += j;

							change = true;
						}
					}

					break;

				skip:;
				}
			}
		}
	}

	return change;
}

static bool moveBranchToExitBlock(DeclFunction *function) {
	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		Ir &branch = function->ops[i];

		if ((isConditionalBranch(branch.type) || branch.type == IrType::GOTO)) {
			u32 exitBlockSize = isExitBlock(function, branch.jumpTarget);


			if (exitBlockSize) {
				u32 start = function->ops.size();

				for (u32 j = branch.jumpTarget; j < branch.jumpTarget + exitBlockSize; j++) {

					function->ops.add(function->ops[j]);
					Ir &op = function->ops[j];

					op.callRegs.storage = nullptr;

					changeToNoop(op);
				}

				for (u32 j = 0; j < function->ops.size(); j++) {
					Ir &op = function->ops[j];

					if (op.jumpTarget >= branch.jumpTarget && op.jumpTarget < branch.jumpTarget + exitBlockSize) {
						op.jumpTarget -= branch.jumpTarget;
						op.jumpTarget += start;
					}
				}

				return true;
			}
		}
	}

	return false;
}

static bool switchJumpsOverExitBlock(DeclFunction *function) {
	for (s32 i = function->ops.size() - 2; i >= 0; i--) {
		Ir &branch = function->ops[i];

		if ((isConditionalBranch(branch.type) || branch.type == IrType::GOTO) && branch.jumpTarget + 1 != function->ops.size() /* @Audit is this sufficient to prevent infinite looping*/) {
			u32 exitBlockSize = isRelocatable(function, i + 1);

			u32 targetSize = isRelocatable(function, branch.jumpTarget);


			if (exitBlockSize) {

				if (targetSize) {
					int aaa = 0;
				}
				else {

					if (branch.jumpTarget == i + 1 + exitBlockSize) {
						branch.type = branch.type == IrType::GOTO ? IrType::NOOP : getOpposite(branch.type);
						branch.jumpTarget = function->ops.size();
						u32 start = function->ops.size();

						for (u32 j = i + 1; j < i + 1 + exitBlockSize; j++) {

							function->ops.add(function->ops[j]);
							Ir &op = function->ops[j];

							op.callRegs.storage = nullptr;

							changeToNoop(op);
						}

						for (u32 j = 0; j < function->ops.size(); j++) {
							Ir &op = function->ops[j];

							if (op.jumpTarget >= i + 1 && op.jumpTarget < i + 1 + exitBlockSize) {
								op.jumpTarget -= i + 1;
								op.jumpTarget += start;
							}
						}

						return true;
					}
				}
			}
		}
	}

	return false;
}

static bool isBranchToExitBlockAndDoesntUse(DeclFunction *function, Ir &branch, Reg &dest) {
	bool overwritten = false;

	for (u32 i = branch.jumpTarget; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		if (op.type == IrType::GOTO || isConditionalBranch(op.type)) {
			return false;
		}

		if (!overwritten) {
			if (op.type == IrType::CALL) {
				for (Reg &reg : op.callRegs) {
					if (reg == dest) {
						return false;
					}
				}
			}
			else {
				for (ulang j = 0; j < op.regCount; j++) {
					if (op.regs[j] == dest) {
						return false;
					}
				}
			}
		}

		if (op.dest == dest) overwritten = true;


		if (op.type == IrType::RETURN) {
			return true;
		}
	}

	return true;
}

static bool inlineGotoRelocatable(DeclFunction *function) {
	bool change = false;

	for (s32 i = 0; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		if (op.type == IrType::GOTO) {
			u32 exitBlockSize = isRelocatable(function, op.jumpTarget);

			if (exitBlockSize && op.jumpTarget + exitBlockSize - 1 != i /*Don't try to unroll infinite loops*/) {
				function->ops.reserve(function->ops.size() + exitBlockSize - 1);

				function->ops.count += exitBlockSize - 1;

				for (s32 j = function->ops.size() - exitBlockSize; j > i; j--) {
					function->ops[j + exitBlockSize - 1] = function->ops[j];
				}

				int a = 0; // dummy to set breakpoint here

				for (u32 j = 0; j < function->ops.size(); j++) {
					Ir &branch = function->ops[j];

					if (branch.jumpTarget > i)
						branch.jumpTarget += exitBlockSize - 1;
				}

				u32 target = op.jumpTarget;

				for (u32 j = 0; j < exitBlockSize; j++) {
					Ir &move = function->ops[target + j];
					Ir &dest = function->ops[i + j];

					if (move.type == IrType::CALL) {
						dest.type = move.type;
						dest.dest = move.dest;
						dest.flags = move.flags;
						dest.regCount = move.regCount;
						dest.callRegs = decltype(dest.callRegs)(std::initializer_list<Reg>(move.callRegs.begin(), move.callRegs.end()));
					}
					else {
						dest = move;
					}
				}

				change = true;
			}
		}
	}

	return change;
}

static bool moveStatementToUse(DeclFunction *function, Array<u32> &usages) {
	PROFILE_FUNC();

	usages.clear();

	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		bool usageFound = false;
		u32 usage = CANT_FIND_USAGE_SENTINEL;

		if (!op.dest) goto done;


		for (usage = i + 1; usage < function->ops.size(); usage++) {
			Ir &use = function->ops[usage];

			if (use.type == IrType::CALL) {
				for (Reg &reg : use.callRegs) {
					if (reg == op.dest) {
						usageFound = true;
						goto done;
					}
				}
			}
			else {
				for (u32 reg = 0; reg < use.regCount; reg++) {
					if (use.regs[reg] == op.dest) {
						usageFound = true;
						goto done;
					}
				}
			}

			if (use.dest) {
				if (op.type == IrType::CALL) {
					for (Reg &reg : op.callRegs) {
						if (reg == use.dest) {
							goto done;
						}
					}
				}
				else {
					for (u32 reg = 0; reg < op.regCount; reg++) {
						if (op.regs[reg] == use.dest) {
							goto done;
						}
					}
				}
			}

			if (use.dest == op.dest || !continuesToNext(use.type) || isConditionalBranch(use.type) || (use.flags & IR_IS_JUMP_TARGET)) {
				break;
			}

			if (use.type == IrType::CALL || use.type == IrType::WRITE) {
				if (op.type == IrType::READ || op.type == IrType::WRITE || op.type == IrType::CALL) {
					break;
				}
			}
			else if (use.type == IrType::READ) {
				if (op.type == IrType::WRITE || op.type == IrType::CALL) {
					break;
				}
			}
		}
	done:

		usages.add(usageFound ? usage : CANT_FIND_USAGE_SENTINEL);
	}

	for (u32 i = 0; i + 1 < function->ops.size(); i++) {
		if (usages[i] == CANT_FIND_USAGE_SENTINEL) continue;

		if (i + 1 < usages[i] && !usagesInSameTree(usages, i + 1, i)) {
			for (u32 j = i; j + 1 < usages[i]; j++) {
				if (usagesInSameTree(usages, i, j + 1)) break;

				std::swap(function->ops[j], function->ops[j + 1]);
			}

			return true;
		}
	}

	return false;
}

static bool moveStatementPastBranch(DeclFunction *function) {
	PROFILE_FUNC();

	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &op = function->ops[i];

		bool branchFound = false;
		u32 branch = CANT_FIND_USAGE_SENTINEL;

		if (!op.dest) goto done;


		for (branch = i + 1; branch < function->ops.size(); branch++) {
			Ir &use = function->ops[branch];

			if (use.type == IrType::CALL) {
				for (Reg &reg : use.callRegs) {
					if (reg == op.dest) {
						goto done;
					}
				}
			}
			else {
				for (u32 reg = 0; reg < use.regCount; reg++) {
					if (use.regs[reg] == op.dest) {
						goto done;
					}
				}
			}

			if (use.dest) {
				if (op.type == IrType::CALL) {
					for (Reg &reg : op.callRegs) {
						if (reg == use.dest) {
							goto done;
						}
					}
				}
				else {
					for (u32 reg = 0; reg < op.regCount; reg++) {
						if (op.regs[reg] == use.dest) {
							goto done;
						}
					}
				}
			}

			if (use.dest == op.dest || !continuesToNext(use.type) || (use.flags & IR_IS_JUMP_TARGET)) {
				break;
			}

			if (isConditionalBranch(use.type)) {
				branchFound = isBranchToExitBlockAndDoesntUse(function, use, op.dest);
				break;
			}

			if (use.type == IrType::CALL || use.type == IrType::WRITE) {
				if (op.type == IrType::READ || op.type == IrType::WRITE || op.type == IrType::CALL) {
					break;
				}
			}
			else if (use.type == IrType::READ) {
				if (op.type == IrType::WRITE || op.type == IrType::CALL) {
					break;
				}
			}
		}
	done:

		if (branchFound) {
			for (u32 j = i + 1; j <= branch; j++) {
				std::swap(function->ops[j - 1], function->ops[j]);
			}

			return true;
		}
	}

	return false;
}

static bool isOutOfBounds(Decl *decl, ulang offset) {
	if (decl->type == DeclType::VAR) {
		return offset != 0;
	}
	else if (decl->type == DeclType::FUNCTION) {
		return true; // Writing to a functions memory is always a yikes
	}
	else if (decl->type == DeclType::ARRAY) {
		return offset >= static_cast<DeclArray *>(decl)->count;
	}
	else if (decl->type == DeclType::STRING) {
		return offset > decl->name.length; // The zero-terminator is within bounds
	}

	return true;
}

static bool couldOverlap(Reg &first, Reg &second) {

	if (first.type != second.type) return true;


	if (first.type == RegType::REGISTER) return true;
	if (first.type == RegType::IMMEDIATE) return first.unumber == second.unumber;

	if (first.type == RegType::STATIC_ADROF) {
		if (first.decl == second.decl) return first.unumber == second.unumber; // If they are the same decl with a different offset they can't overlap

		if (first.decl->type == DeclType::STRING && second.decl->type == DeclType::STRING) return true; // String literals may be overlapped in memory

		return isOutOfBounds(first.decl, first.unumber) || isOutOfBounds(second.decl, second.unumber);
	}

	return true;
}

static bool optimizeMemoryAccessInBasicBlock(DeclFunction *function, u32 *index) {
	PROFILE_FUNC();
	u32 end = function->ops.size();

	for (u32 i = *index + 1; i < end; i++) {
		if (function->ops[i].flags & IR_IS_JUMP_TARGET) {
			end = i;
			break;
		}
	}

	bool change = false;

	for (u32 propagate = *index; propagate < end; propagate++) {
		Ir &prop = function->ops[propagate];

		switch (prop.type) {
			case IrType::WRITE: {
				bool canRemoveWrite = true;

				for (u32 i = propagate + 1; i < end; i++) {
					Ir &op = function->ops[i];

					if (op.type == IrType::READ && op.regs[0] == prop.regs[0]) {
						op.type = IrType::SET;
						op.regs[0] = prop.regs[1];
						change = true;
					}


					if (canRemoveWrite && op.type == IrType::WRITE && op.regs[0] == prop.regs[0]) {
						changeToNoop(op);
						change = true;
						break;
					}

					if (op.dest == prop.regs[1]) break;
					if (op.dest == prop.regs[0]) break;
					if (op.type == IrType::WRITE && couldOverlap(op.regs[0], prop.regs[0])) break;
					if (op.type == IrType::CALL) break;
					if (op.type == IrType::READ && couldOverlap(op.regs[0], prop.regs[0])) canRemoveWrite = false;
					if (isConditionalBranch(op.type)) canRemoveWrite = false;
					//if (op.type == IrType::WRITE && op.regs[0].type == RegType::)
					// if (op.dest && op.dest.unumber == prop.regs[0].unumber) break;
				}

				break;
			}
			case IrType::READ: {
				for (u32 i = propagate + 1; i < end; i++) {
					Ir &op = function->ops[i];

					if (op.type == IrType::READ && op.regs[0] == prop.regs[0]) {
						op.type = IrType::SET;
						op.regs[0] = prop.dest;
						change = true;
					}

					if (op.dest == prop.dest) break;
					if (op.dest == prop.regs[0]) break;
					if (op.type == IrType::WRITE && couldOverlap(op.regs[0], prop.regs[0])) break;
					if (op.type == IrType::CALL) break;
					//if (op.type == IrType::WRITE && op.regs[0].type == RegType::)
					// if (op.dest && op.dest.unumber == prop.regs[0].unumber) break;
				}

				break;
			}
		}
	}

	*index = end;
	return change;
}

static bool optimizeMemoryAccess(DeclFunction *function) {
	PROFILE_FUNC();
	bool change = false;

	u32 index = 0;

	while (index != function->ops.size()) {
		change |= optimizeMemoryAccessInBasicBlock(function, &index);
	}

	return change;
}

static bool addConstraint(Constraints &dest, Constraint src) {
	assert(src.min <= src.max);

	if (src.min == ULANG_MIN && src.max == ULANG_MAX) {
		bool result = dest.size() != 1 || dest[0].min != 0 || dest[0].max != ULANG_MAX;

		dest.clear();
		dest.add(src);
		return result;
	}

	PROFILE_ZONE();

	ulang min = src.min == 0 ? 0 : src.min - 1;
	ulang max = src.max == ULANG_MAX ? ULANG_MAX : src.max + 1;

	for (u32 i = 0; i < dest.size(); i++) {

		if (min <= dest[i].max && dest[i].min <= max) {
			Constraint newC = { my_min(src.min, dest[i].min), my_max(src.max, dest[i].max) };

			if (newC != dest[i]) {
				dest.unordered_remove(i);
				addConstraint(dest, newC); // If we had 3 <= x <= 7 and 9 <= x <= 11 before and we add 6 <= x <= 10 we need to make sure we get 3 <= x <= 11

				return true;
			}

			return false;
		}
	}

	dest.add(src);
	return true;
}

static bool addConstraints(Constraints &dest, Constraints &src) {
	bool change = false;

	for (u32 i = 0; i < src.size(); i++) {
		change |= addConstraint(dest, src[i]);
	}

	return change;
}

static Constraints getArgConstraints(Ir &op, u32 param, Constraints *state) {
	Reg reg;

	if (op.type == IrType::CALL) {
		reg = op.callRegs[param];
	}
	else {
		reg = op.regs[param];
	}

	if (reg.type == RegType::IMMEDIATE) {
		return { {reg.unumber, reg.unumber} };
	}
	else if (reg.type == RegType::REGISTER) {
		return state[reg.unumber];
	}
	else {
		return { {ULANG_MIN, ULANG_MAX} };
	}
}

static void constraintsForSignedIf(const Constraints &a, Constraints &state, Constraints &newState, slang min, slang max) {
	if (a.size()) {
		for (u32 i = 0; i < a.size(); i++) {
			if (a[i].min <= SLANG_MAX && a[i].max > SLANG_MAX) {

				if (min < 0) {
					if ((slang) a[i].max >= min) {
						newState.add({ a[i].min, SLANG_MAX });
						newState.add({ (ulang) min, a[i].max });
					}
					else {
						newState.add({ a[i].min, SLANG_MAX });
					}
				}
				else {
					newState.add({ my_max(a[i].min, (ulang) min), SLANG_MAX });
				}


				if (max >= 0) {
					if ((slang) a[i].min <= max) {
						state.add({ a[i].min, (ulang) max });
						state.add({ (ulang) SLANG_MIN, a[i].max });
					}
					else {
						state.add({ (ulang) SLANG_MIN, a[i].max });
					}
				}
				else {
					state.add({ (ulang) SLANG_MIN, my_min(a[i].max,(ulang) max) });
				}
			}
			else {
				if ((slang) a[i].max >= min) {
					newState.add({ (ulang) my_max((slang) a[i].min, min), a[i].max });
				}

				if ((slang) a[i].min <= max) {
					state.add({ a[i].min, (ulang) my_min((slang) a[i].max, max) });
				}
			}
		}
	}
	else {
		if (min < 0) {
			newState.add({ (ulang) min, ULANG_MAX });
			newState.add({ 0, SLANG_MAX });
		}
		else {
			newState.add({ (ulang) min, SLANG_MAX });
		}

		if (max >= 0) {
			state.add({ (ulang) SLANG_MIN, ULANG_MAX });
			state.add({ 0, (ulang) max });
		}
		else {
			state.add({ (ulang) SLANG_MIN, (ulang) max });
		}
	}
}

static void constraintsForIfG(const Constraints &a, const Constraints &b, Constraints &state, Constraints &newState) {

	slang min = SLANG_MAX;
	slang max = SLANG_MIN;

	for (u32 i = 0; i < b.size(); i++) {
		if (b[i].min <= SLANG_MAX && b[i].max > SLANG_MAX) {
			min = SLANG_MIN;
			max = SLANG_MAX;
		}
		else {
			min = my_min(min, (slang) b[i].min);
			max = my_max(max, (slang) b[i].max);
		}
	}

	if (min != SLANG_MAX) {
		++min;

		constraintsForSignedIf(a, state, newState, min, max);
	}
}

static void constraintsForIfGE(const Constraints &a, const Constraints &b, Constraints &state, Constraints &newState) {

	slang min = SLANG_MAX;
	slang max = SLANG_MIN;

	for (u32 i = 0; i < b.size(); i++) {
		if (b[i].min <= SLANG_MAX && b[i].max > SLANG_MAX) {
			min = SLANG_MIN;
			max = SLANG_MAX;
		}
		else {
			min = my_min(min, (slang) b[i].min);
			max = my_max(max, (slang) b[i].max);
		}
	}

	if (max != SLANG_MIN) {
		--max;

		constraintsForSignedIf(a, state, newState, min, max);
	}
}

static void constraintsForUnsignedIf(const Constraints &a, Constraints &state, Constraints &newState, ulang min, ulang max) {
	if (a.size()) {
		for (u32 i = 0; i < a.size(); i++) {
			if (a[i].max >= min) {
				newState.add({ my_max(a[i].min, min), a[i].max });
			}

			if (a[i].min <= max) {
				state.add({ a[i].min, my_min(a[i].max, max) });
			}
		}
	}
	else {
		newState.add({ min, ULANG_MAX });

		state.add({ 0, max });
	}
}

static void constraintsForIfA(const Constraints &a, const Constraints &b, Constraints &state, Constraints &newState) {

	ulang min = ULANG_MAX;
	ulang max = ULANG_MIN;

	for (u32 i = 0; i < b.size(); i++) {
		min = my_min(min, b[i].min);
		max = my_max(max, b[i].max);
	}

	if (min != ULANG_MAX) {
		++min;

		constraintsForUnsignedIf(a, state, newState, min, max);
	}
}

static void constraintsForIfAE(Constraints &a, Constraints &b, Constraints &state, Constraints &newState) {

	ulang min = ULANG_MAX;
	ulang max = ULANG_MIN;

	for (u32 i = 0; i < b.size(); i++) {
		min = my_min(min, b[i].min);
		max = my_max(max, b[i].max);
	}

	if (max != ULANG_MIN) {
		--max;

		constraintsForUnsignedIf(a, state, newState, min, max);
	}
}

static void constraintsForIfEq(Constraints &nextState, Constraints &branchState, Constraints &left, Constraints &right) {
	for (auto c1 : left) {
		for (auto c2 : right) {
			if (c1.min <= c2.max && c2.min <= c1.max) {
				branchState.add({ my_max(c1.min, c2.min), my_min(c1.max, c2.max) });
			}
		}
	}

	if (right.size() == 1 && right[0].min == right[0].max) {
		ulang val = right[0].min;

		for (auto c : left) {
			if (c.min == c.max && c.min == val) {
			}
			else if (c.min == val) {
				nextState.add({ c.min + 1u, c.max });
			}
			else if (c.max == val) {
				nextState.add({ c.min, c.max - 1u });
			}
			else if (val > c.min &&val < c.max) {
				nextState.add({ c.min, val - 1u });
				nextState.add({ val + 1u, c.max });
			}
			else {
				nextState.add({ c.min, c.max });
			}
		}
	}
	else {
		for (auto c : left) nextState.add(c);
	}
}

static void constraintsForConditionalBranch(Ir &op, Constraints *state, Constraints &leftState, Constraints &leftBranchState, Constraints &rightState, Constraints &rightBranchState) {
	if (op.type == IrType::IF_Z || op.type == IrType::IF_NZ) {
		if (op.regs[0].type == RegType::REGISTER) {
			leftState.clear();
			leftBranchState.clear();

			if (op.type == IrType::IF_Z) {
				leftBranchState.add({ 0, 0 });

				for (auto constraint : state[op.regs[0].unumber]) {
					if (constraint.max != 0) {
						leftState.add({ constraint.min == 0 ? 1u : constraint.min, constraint.max });
					}
				}
			}
			else if (op.type == IrType::IF_NZ) {

				addConstraint(leftState, { 0, 0 });

				for (auto constraint : state[op.regs[0].unumber]) {
					if (constraint.max != 0) {
						leftBranchState.add({ constraint.min == 0 ? 1u : constraint.min, constraint.max });
					}
				}
			}
		}
	}
	else {
		assert(isConditionalBranch(op.type));

		leftState.clear();
		leftBranchState.clear();
		rightState.clear();
		rightBranchState.clear();

		Constraints left = getArgConstraints(op, 0, state);
		Constraints right = getArgConstraints(op, 1, state);

		switch (op.type) {
			case IrType::IF_EQ: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfEq(leftState, leftBranchState, left, right);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfEq(rightState, rightBranchState, right, left);
				}

				break;
			}
			case IrType::IF_NEQ: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfEq(leftBranchState, leftState, left, right);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfEq(rightBranchState, rightState, right, left);
				}

				break;
			}
			case IrType::IF_G: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfG(left, right, leftState, leftBranchState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfGE(right, left, rightBranchState, rightState);
				}

				break;
			}
			case IrType::IF_LE: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfG(left, right, leftBranchState, leftState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfGE(right, left, rightState, rightBranchState);
				}

				break;
			}
			case IrType::IF_L: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfGE(left, right, leftBranchState, leftState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfG(right, left, rightState, rightBranchState);
				}

				break;
			}
			case IrType::IF_GE: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfGE(left, right, leftState, leftBranchState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfG(right, left, rightBranchState, rightState);
				}

				break;
			}
			case IrType::IF_A: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfA(left, right, leftState, leftBranchState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfAE(right, left, rightBranchState, rightState);
				}

				break;
			}
			case IrType::IF_BE: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfA(left, right, leftBranchState, leftState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfAE(right, left, rightState, rightBranchState);
				}

				break;
			}
			case IrType::IF_B: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfAE(left, right, leftBranchState, leftState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfA(right, left, rightState, rightBranchState);
				}

				break;
			}
			case IrType::IF_AE: {
				if (op.regs[0].type == RegType::REGISTER) {
					constraintsForIfAE(left, right, leftState, leftBranchState);
				}

				if (op.regs[1].type == RegType::REGISTER) {
					constraintsForIfA(right, left, rightBranchState, rightState);
				}

				break;
			}
			case IrType::IF_AND_Z:
			case IrType::IF_AND_NZ: {

				if (op.regs[0].type == RegType::REGISTER) {
					for (auto &constraint : state[op.regs[0].unumber]) {
						leftState.add(constraint);
						leftBranchState.add(constraint);
					}
				}

				if (op.regs[1].type == RegType::REGISTER) {
					for (auto &constraint : state[op.regs[1].unumber]) {
						rightState.add(constraint);
						rightBranchState.add(constraint);
					}
				}

				break;
			}
			default:
				assert(false);
				break;
		}
	}
}

void calculateConstraints(DeclFunction *function, Constraints *constraints) {
	PROFILE_FUNC();

	assert(function->ops.size()); // We should always have a return

	for (u32 i = 0; i <= function->largestReg; i++) {
		constraints[i].clear();
		constraints[i].add({ ULANG_MIN, ULANG_MAX });
	}

	for (u32 i = function->largestReg + 1; i < (function->largestReg + 1) * function->ops.size(); i++) {
		constraints[i].clear();
	}

	u32 backtrackCount = 0;

	Constraints leftState;
	Constraints leftBranchState;

	Constraints rightState;
	Constraints rightBranchState;
	bool needRepeat = true;

	while (needRepeat) {
		PROFILE_ZONE("calculateConstraints iteration");
		needRepeat = false;

		for (u32 idx = 0; idx < function->ops.size(); idx++) {

			Ir &op = function->ops[idx];

			Constraints *state = constraints + (function->largestReg + 1ULL) * idx;

			Constraints *nextState = state + (function->largestReg + 1ULL);
			Constraints *branchState = constraints + (function->largestReg + 1ULL) * op.jumpTarget;


			if (op.dest) {
				for (u32 i = 0; i <= function->largestReg; i++) {
					if (i != op.dest.unumber) {
						addConstraints(nextState[i], state[i]);
					}
				}

				if (nextState[op.dest.unumber].size() == 1 && nextState[op.dest.unumber][0].min == 0 && nextState[op.dest.unumber][0].max == ULANG_MAX) {
					continue;
				}

				leftState.clear();

				switch (op.type) {
					case IrType::EQ:
					case IrType::NOT_EQ:
					case IrType::GREATER:
					case IrType::LESS_EQUAL:
					case IrType::LESS:
					case IrType::GREATER_EQUAL:
					case IrType::ABOVE:
					case IrType::BELOW_EQUAL:
					case IrType::BELOW:
					case IrType::ABOVE_EQUAL: {
						leftState.add({ 0, 1 });
						break;
					}
					case IrType::SET: {
						for (auto c : getArgConstraints(op, 0, state)) leftState.add(c);

						break;
					}

					case IrType::MOD: {
						Constraints left = getArgConstraints(op, 0, state);
						Constraints right = getArgConstraints(op, 1, state);

						slang maxAbs = -1; // Use negative of abs value so we can include SLANG_MIN

						for (auto c : right) {
							if (c.min <= SLANG_MAX && c.max > SLANG_MAX) {
								maxAbs = SLANG_MIN;
								break;
							}

							slang min = (slang) c.min;
							slang max = (slang) c.max;

							maxAbs = my_min(maxAbs, min < 0 ? min : -min);
							maxAbs = my_min(maxAbs, max < 0 ? max : -max);
						}


						bool alwaysPositive = true;
						bool alwaysNegative = true;

						for (auto c : left) {
							if ((slang) c.min < 0) {
								alwaysPositive = false;
							}
							else {
								alwaysNegative = false;
							}

							if ((slang) c.max < 0) {
								alwaysPositive = false;
							}
							else {
								alwaysNegative = false;
							}
						}

						if (alwaysPositive) {
							leftState.add({ 0, (ulang) -(maxAbs + 1) });
						}
						else if (alwaysNegative) {
							leftState.add({ (ulang) (maxAbs + 1), ULANG_MAX });
							leftState.add({ 0, 0 });
						}
						else {
							leftState.add({ (ulang) (maxAbs + 1), ULANG_MAX });
							leftState.add({ 0, (ulang) -(maxAbs + 1) });
						}

						break;
					}
					case IrType::NEG: {
						Constraints left = getArgConstraints(op, 0, state);

						for (auto c : left) {
							if ((ulang) -c.max > (ulang) -c.min) {
								addConstraint(leftState, { (ulang) -c.max, ULANG_MAX });
								addConstraint(leftState, { 0, (ulang) -c.min });
							}
							else {
								addConstraint(leftState, { (ulang) -c.max, (ulang) -c.min });
							}
						}

						break;
					}
					case IrType::ADD: {
						if (backtrackCount > maxBracktrackCountForComplexConstraints) goto simple;

						Constraints left = getArgConstraints(op, 0, state);
						Constraints right = getArgConstraints(op, 1, state);

						for (auto l : left) {
							for (auto r : right) {
								u32 min = (u32) l.min + (u32) r.min;
								u32 max = (u32) l.max + (u32) r.max;

								if (max > ULANG_MAX &&min <= ULANG_MAX) {
									leftState.add({ (ulang) min, ULANG_MAX });
									leftState.add({ 0, (ulang) max });
								}
								else {
									leftState.add({ (ulang) min, (ulang) max });
								}
							}
						}

						break;
					}
					default: {
					simple:
						leftState.add({ ULANG_MIN, ULANG_MAX });
						break;
					}
				}

				assert(idx != function->ops.size()); // The last op in a function should be a return or goto so we should never get here

				addConstraints(nextState[op.dest.unumber], leftState);
			}
			else if (op.type == IrType::RETURN) {
				// We are done since there is no next state to update
			}
			else if (op.type == IrType::GOTO) {
				for (u32 i = 0; i <= function->largestReg; i++) {
					needRepeat |= addConstraints(branchState[i], state[i]) && op.jumpTarget < idx;
				}
			}
			else if (isConditionalBranch(op.type)) {
				constraintsForConditionalBranch(op, state, leftState, leftBranchState, rightState, rightBranchState);

				if (op.regCount == 1) {
					for (u32 i = 0; i <= function->largestReg; i++) {
						if (i != op.regs[0].unumber) {
							addConstraints(nextState[i], state[i]);
							needRepeat |= addConstraints(branchState[i], state[i]) && op.jumpTarget < idx;
						}
					}

					addConstraints(nextState[op.regs[0].unumber], leftState);
					needRepeat |= addConstraints(branchState[op.regs[0].unumber], leftBranchState) && op.jumpTarget < idx;
				}
				else {
					for (u32 i = 0; i <= function->largestReg; i++) {
						if (op.regs[0].type == RegType::REGISTER && op.regs[0].unumber == i) continue;
						if (op.regs[1].type == RegType::REGISTER && op.regs[1].unumber == i) continue;

						addConstraints(nextState[i], state[i]);
						needRepeat |= addConstraints(branchState[i], state[i]) && op.jumpTarget < idx;
					}

					if (op.regs[0].type == RegType::REGISTER) {
						addConstraints(nextState[op.regs[0].unumber], leftState);
						needRepeat |= addConstraints(branchState[op.regs[0].unumber], leftBranchState) && op.jumpTarget < idx;
					}

					if (op.regs[1].type == RegType::REGISTER) {
						addConstraints(nextState[op.regs[1].unumber], rightState);
						needRepeat |= addConstraints(branchState[op.regs[1].unumber], rightBranchState) && op.jumpTarget < idx;
					}
				}
			}
			else {
				for (u32 i = 0; i <= function->largestReg; i++) {
					addConstraints(nextState[i], state[i]);
				}
			}
		}

		++backtrackCount;
	}


	rightBranchState.free();
	rightState.free();

	leftBranchState.free();
	leftState.free();
}

static void printReg(Reg &reg) {
	switch (reg.type) {
		case RegType::REGISTER:
			irOutput << " R" << reg.unumber;
			break;
		case RegType::STATIC_ADROF:
			irOutput << " S:";
			if (reg.decl->flags & DECL_IS_LOCAL) {
				irOutput << getFilename(reg.decl->startLocation.fileUid) << '$';
			}

			irOutput << reg.decl->name;

			if (reg.number) {
				irOutput << ':' << reg.number;
			}
			break;
		case RegType::IMMEDIATE:
			irOutput << ' ' << reg.number;
			break;
	}
}

#define sminmax()\
	Constraints a = getArgConstraints(op, 0, state);\
	Constraints b = getArgConstraints(op, 1, state);\
\
	slang aMin = SLANG_MAX;\
	slang aMax = SLANG_MIN;\
\
	for (auto c : a) {\
		if (c.min <= SLANG_MAX && c.max > SLANG_MAX) {\
			aMin = SLANG_MIN;\
			aMax = SLANG_MAX;\
			break;\
		}\
		else {\
			aMin = my_min((slang) c.min, aMin);\
			aMax = my_max((slang) c.max, aMax);\
		}\
	}\
\
	slang bMin = SLANG_MAX;\
	slang bMax = SLANG_MIN;\
	\
\
	for (auto c : b) {\
		if (c.min <= SLANG_MAX && c.max > SLANG_MAX) {\
			bMin = SLANG_MIN;\
			bMax = SLANG_MAX;\
			break;\
		}\
		else {\
			bMin = my_min((slang) c.min, bMin);\
			bMax = my_max((slang) c.max, bMax);\
		}\
	}\

#define uminmax()\
	Constraints a = getArgConstraints(op, 0, state);\
	Constraints b = getArgConstraints(op, 1, state);\
\
	ulang aMin = ULANG_MAX;\
	ulang aMax = ULANG_MIN;\
\
	for (auto c : a) {\
		aMin = my_min(c.min, aMin);\
		aMax = my_max(c.max, aMax);\
	}\
\
	ulang bMin = ULANG_MAX;\
	ulang bMax = ULANG_MIN;\
	\
\
	for (auto c : b) {\
		bMin = my_min(c.min, bMin);\
		bMax = my_max(c.max, bMax);\
	}\


static bool constraintsForCondition(Ir &op, Constraints *state, bool *met) {
	switch (op.type) {
		case IrType::IF_Z: {
			for (auto c : getArgConstraints(op, 0, state)) {
				if (c.min == 0) return false;
			}

			*met = false;
			return true;
		}
		case IrType::IF_NZ: {
			for (auto c : getArgConstraints(op, 0, state)) {
				if (c.min == 0) return false;
			}

			*met = true;
			return true;
		}
		case IrType::EQ:
		case IrType::IF_EQ: {
			Constraints a = getArgConstraints(op, 0, state);
			Constraints b = getArgConstraints(op, 1, state);

			for (auto c1 : a) {
				for (auto c2 : b) {
					if (c1.min <= c2.max && c2.min <= c1.max) return false;
				}
			}

			*met = false;
			return true;
		}
		case IrType::NOT_EQ:
		case IrType::IF_NEQ: {
			Constraints a = getArgConstraints(op, 0, state);
			Constraints b = getArgConstraints(op, 1, state);

			for (auto c1 : a) {
				for (auto c2 : b) {
					if (c1.min <= c2.max && c2.min <= c1.max) return false;
				}
			}

			*met = true;
			return true;
		}
		case IrType::GREATER:
		case IrType::IF_G: {
			sminmax();

			if (aMin > bMax) {
				*met = true;
				return true;
			}
			else if (aMax <= bMin) {
				*met = false;
				return true;
			}

			return false;
		}
		case IrType::LESS_EQUAL:
		case IrType::IF_LE: {
			sminmax();

			if (aMin > bMax) {
				*met = false;
				return true;
			}
			else if (aMax <= bMin) {
				*met = true;
				return true;
			}

			return false;
		}
		case IrType::LESS:
		case IrType::IF_L: {
			sminmax();

			if (aMax < bMin) {
				*met = true;
				return true;
			}
			else if (aMin >= bMax) {
				*met = false;
				return true;
			}

			return false;
		}
		case IrType::GREATER_EQUAL:
		case IrType::IF_GE: {
			sminmax();

			if (aMax < bMin) {
				*met = false;
				return true;
			}
			else if (aMin >= bMax) {
				*met = true;
				return true;
			}

			return false;
		}
		case IrType::ABOVE:
		case IrType::IF_A: {
			uminmax();

			if (aMin > bMax) {
				*met = true;
				return true;
			}
			else if (aMax <= bMin) {
				*met = false;
				return true;
			}

			return false;
		}
		case IrType::BELOW_EQUAL:
		case IrType::IF_BE: {
			uminmax();

			if (aMin > bMax) {
				*met = false;
				return true;
			}
			else if (aMax <= bMin) {
				*met = true;
				return true;
			}

			return false;
		}
		case IrType::BELOW:
		case IrType::IF_B: {
			uminmax();

			if (aMax < bMin) {
				*met = true;
				return true;
			}
			else if (aMin >= bMax) {
				*met = false;
				return true;
			}

			return false;
		}
		case IrType::ABOVE_EQUAL:
		case IrType::IF_AE: {
			uminmax();

			if (aMax < bMin) {
				*met = false;
				return true;
			}
			else if (aMin >= bMax) {
				*met = true;
				return true;
			}

			return false;
		}
		case IrType::IF_AND_NZ:
		case IrType::IF_AND_Z: {
			return false;
		}
	}

	return false;
}

#undef sminmax
#undef uminmax

static bool optimizeConstraints(DeclFunction *function, Constraints **constraintsAllocation, u32 constraintsSize) {
	PROFILE_FUNC();

	Constraints *constraints = *constraintsAllocation;

	if (constraintsSize < (function->largestReg + 1ULL) * function->ops.size()) {
		u64 newSize = my_max(constraintsSize * 2ULL,
			(function->largestReg + 1ULL) * function->ops.size());

		*constraintsAllocation = constraints = static_cast<decltype(constraints)>(realloc(constraints, sizeof(constraints[0]) * newSize));

		for (u64 i = constraintsSize; i < newSize; i++) {
			new (constraints + i) Constraints;
		}
	}
	
	calculateConstraints(function, constraints);

	bool change = false;

	Constraints leftState;
	Constraints leftBranchState;
	Constraints rightState;
	Constraints rightBranchState;

	for (u32 i = 0; i < function->ops.size(); i++) {
		Constraints *state = constraints + (function->largestReg + 1ULL) * i;

		Ir &op = function->ops[i];

		if (op.type == IrType::CALL) {
			for (Reg &reg : op.callRegs) {
				if (reg.type == RegType::REGISTER) {
					Constraints &s = state[reg.unumber];

					if (s.size() == 1 && s[0].min == s[0].max) {
						reg.type = RegType::IMMEDIATE;
						reg.unumber = s[0].min;
						change = true;
					}
				}
			}
		}
		else {
			for (ulang j = 0; j < op.regCount; j++) {
				Reg &reg = op.regs[j];

				if (reg.type == RegType::REGISTER) {
					Constraints &s = state[reg.unumber];

					if (s.size() == 1 && s[0].min == s[0].max) {
						reg.type = RegType::IMMEDIATE;
						reg.unumber = s[0].min;
						change = true;
					}
				}
			}

		}

		if (isConditionalBranch(op.type)) {
			bool taken;

			if (constraintsForCondition(op, state, &taken)) {
				op.regCount = 0;
				op.type = taken ? IrType::GOTO : IrType::NOOP;
				change = true;
			}
		}

		if (isConditionalBranch(op.type) || op.type == IrType::GOTO) {
			Ir &target = function->ops[op.jumpTarget];

			if (isConditionalBranch(target.type)) {
				Constraint *leftOldStorage = nullptr;
				u32 leftOldCount = 0;
				Constraint *rightOldStorage = nullptr;
				u32 rightOldCount = 0;

				if (op.type != IrType::GOTO && op.type != IrType::IF_AND_Z && op.type != IrType::IF_AND_NZ) {
					constraintsForConditionalBranch(op, state, leftState, leftBranchState, rightState, rightBranchState);

					leftOldStorage = state[op.regs[0].unumber].storage;
					leftOldCount = state[op.regs[0].unumber].count;

					state[op.regs[0].unumber].storage = leftBranchState.begin();
					state[op.regs[0].unumber].count = leftBranchState.count;

					if (op.regCount == 2 && op.regs[1].type == RegType::REGISTER) {
						rightOldStorage = state[op.regs[1].unumber].storage;
						rightOldCount = state[op.regs[1].unumber].count;

						state[op.regs[1].unumber].storage = rightBranchState.begin();
						state[op.regs[1].unumber].count = rightBranchState.count;
					}
				}

				bool taken;
				if (constraintsForCondition(target, state, &taken)) {
					op.jumpTarget = taken ? target.jumpTarget : op.jumpTarget + 1;
					change = true;
				}

				if (op.type != IrType::GOTO) {
					state[op.regs[0].unumber].storage = leftOldStorage;
					state[op.regs[0].unumber].count = leftOldCount;

					if (op.regCount == 2 && op.regs[1].type == RegType::REGISTER) {
						state[op.regs[1].unumber].storage = rightOldStorage;
						state[op.regs[1].unumber].count = rightOldCount;
					}
				}
			}
		}

		if (isCompare(op.type)) {
			bool one;

			if (constraintsForCondition(op, state, &one)) {
				op.regCount = 1;
				op.type = IrType::SET;
				op.regs[0].type = RegType::IMMEDIATE;
				op.regs[0].number = one ? 1 : 0;

				change = true;
			}
		}
	}

	rightBranchState.free();
	rightState.free();
	leftBranchState.free();
	leftState.free();

	return change;
}

static bool hasSingleWrite(DeclFunction *function, Reg &reg, bool loopMatters) {
	u32 write;

	for (write = 0; write < function->ops.size(); write++) {
		if (function->ops[write].dest == reg) {
			if (loopMatters && (function->ops[write].flags & IR_IS_IN_LOOP)) {
				return false;
			}
			else {
				break;
			}
			
		}
	}

	for (write++; write < function->ops.size(); write++) {
		if (function->ops[write].dest == reg) 
			return false;
	}

	return true;
}

static bool propagateConstantsGlobally(DeclFunction *function) {
	PROFILE_FUNC();
	calculateInLoop(function);

	bool change = false;

	for (u32 i = 0; i < function->ops.size(); i++) {
		Ir &constant = function->ops[i];
		
		if (constant.type == IrType::SET) {
			if (hasSingleWrite(function, constant.dest, false) && (constant.regs[0].type != RegType::REGISTER || hasSingleWrite(function, constant.regs[0], true))) {
				for (u32 j = 0; j < function->ops.size(); j++) {
					Ir &op = function->ops[j];

					if (op.type == IrType::CALL) {
						for (Reg &reg : op.callRegs) {
							if (reg == constant.dest) {
								reg = constant.regs[0];
								change = true;
							}
						}
					}
					else {
						for (ulang reg = 0; reg < op.regCount; reg++) {
							if (op.regs[reg] == constant.dest) {
								op.regs[reg] = constant.regs[0];
								change = true;
							}
						}
					}
				}
			}
		}
		else if (isCompare(constant.type) || constant.type == IrType::AND) {
			if (hasSingleWrite(function, constant.dest, false))
				if ((constant.regs[0].type != RegType::REGISTER || hasSingleWrite(function, constant.regs[0], true)) && 
				(constant.regs[1].type != RegType::REGISTER || hasSingleWrite(function, constant.regs[1], true))) {
				for (u32 j = 0; j < function->ops.size(); j++) {
					Ir &op = function->ops[j];

					if ((op.type == IrType::IF_Z || op.type == IrType::IF_NZ) && op.regs[0] == constant.dest) {
						switch (constant.type) {
							case IrType::GREATER:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_G : IrType::IF_LE;
								break;
							case IrType::LESS_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_LE : IrType::IF_G;
								break;
							case IrType::LESS:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_L : IrType::IF_GE;
								break;
							case IrType::GREATER_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_GE : IrType::IF_L;
								break;
							case IrType::ABOVE:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_A : IrType::IF_BE;
								break;
							case IrType::BELOW_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_BE : IrType::IF_A;
								break;
							case IrType::BELOW:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_B : IrType::IF_AE;
								break;
							case IrType::ABOVE_EQUAL:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_AE : IrType::IF_B;
								break;
							case IrType::EQ:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_EQ : IrType::IF_NEQ;
								break;
							case IrType::NOT_EQ:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_NEQ : IrType::IF_EQ;
								break;
							case IrType::AND:
								op.type = op.type == IrType::IF_NZ ? IrType::IF_AND_NZ : IrType::IF_AND_Z;
								break;
							default:
								assert(false);
						}

						op.regCount = 2;
						op.regs[0] = constant.regs[0];
						op.regs[1] = constant.regs[1];

						change = true;
					}
				}
			}
		}
	}

	return change;
}

void runOptimizer() {
	PROFILE_FUNC();


	Compiler compiler;
	ArraySet<ulang> registersUsed;
	Array<u32> usages;

	u64 *liveRangeBits = nullptr;
	u64 *interferenceBits = nullptr;
	Constraints *constraints = nullptr;

	u64 liveRangeBitsSize = 0;
	u64 interferenceBitsSize = 0;
	u64 constraintsSize = 0;

	while (true) {
		DeclFunction *function = optimizerQueue.take();

		if (!function) {
			optimizerQueue.add(function); // Put the terminator back so the other optimizer threads will stop
			break;
		}

		compiler.generateIr(function);

		{
			PROFILE_ZONE("Basic optimizations");
			do {
				canonize(function);
				calculateLeaders(function);

			} while (removeNoops(function)
				|| deleteUnreachable(function)
				|| basicThreadJumps(function)
				);


			reduceRegisterNumbers(function, registersUsed, compiler.argCount);

			canonize(function);

			if (!(function->flags & DECL_FUNCTION_RETURN_TYPE_IS_KNOWN)) {
				function->flags |= DECL_FUNCTION_IS_VOID | DECL_FUNCTION_RETURN_TYPE_IS_KNOWN;
			}

			if (function->flags & DECL_FUNCTION_IS_VOID) {
				makeReturn(function->ops); // We can't start generating code until the function 
			}
			else {
				// Now that we check hadError to see if we should actually write a binary out, we can't defer this check as the binary could be written before the check completes and is 

				// @Improvement maybe defer this check until after we submit for code generation, since if this check fails we stop compilation
				// so execution spilling over doesn't matter. This will only improve startup/drainout as this pipeline section will have
				// less latency but the same throughput :DeferredChecks

				if (!doesReturn(function->ops)) {
					reportError(function, "Not all control paths return");
					goto error;
				}
			}
		}

		if (!optimizationSettings.advancedOptimizations || !optimizationSettings.allocateRegisters) {
			function->shuffle = nullptr;
		}

		if (optimizationSettings.advancedOptimizations) {
			PROFILE_ZONE("Advanced optimizations");

			bool leadersDirty = true;
			bool canonizeDirty = true;

			do {
				if (canonizeDirty) {
					canonize(function);
					canonizeDirty = false;
				}
				if (leadersDirty) {
					calculateLeaders(function);
					leadersDirty = false;
				}
			} while (false
				|| removeNoops(function)
				|| deleteUnreachable(function)
				|| (basicThreadJumps(function) && (leadersDirty = true))
				|| (optimizationSettings.propagateConstants && propagateInBasicBlocks(function) && (canonizeDirty = true, leadersDirty = true))
				|| (optimizationSettings.simplifyConstantExpressions && simplifyConstantExpressions(function) && (canonizeDirty = true, leadersDirty = true))
				|| optimizeMemoryAccess(function)
				|| removeNeverUsed(function)
				|| (optimizationSettings.deduplicate && removeCommonExpressions(function))
				|| (optimizationSettings.deduplicate && moveDuplicateOutOfBranch(function) && (leadersDirty = true))
				|| (optimizationSettings.deduplicate && moveDuplicateOutOfBranchSlow(function) && (leadersDirty = true))
				|| (optimizationSettings.moveStatementToUse && switchJumpsOverExitBlock(function) && (leadersDirty = true))
				|| (optimizationSettings.moveStatementToUse && inlineGotoRelocatable(function) && (leadersDirty = true))
				|| (optimizationSettings.moveStatementToUse && moveOverwritePastUse(function))
				|| (optimizationSettings.moveStatementToUse && moveStatementToUse(function, usages) && (leadersDirty = true))
				|| (optimizationSettings.moveStatementToUse && moveStatementPastBranch(function) && (leadersDirty = true))
				|| (optimizationSettings.deduplicate && propagateConstantsGlobally(function) && (canonizeDirty = true))
				|| (reduceRegisterNumbers(function, registersUsed, compiler.argCount),
				(optimizationSettings.useConstraints && optimizeConstraints(function, &constraints, constraintsSize) && (canonizeDirty = true, leadersDirty = true)))
				|| (optimizationSettings.deduplicate && deduplicate(function) && (leadersDirty = true))
				);

			reduceRegisterNumbers(function, registersUsed, compiler.argCount);

			u64 requiredSize = getRequiredLiveRangeInfoSize(function);
			if (liveRangeBitsSize < requiredSize) {
				free(liveRangeBits);
				liveRangeBitsSize = my_max(requiredSize, liveRangeBitsSize * 2);

				liveRangeBits = static_cast<u64 *>(malloc(liveRangeBitsSize * sizeof(u64)));
			}


			calculateLiveRanges(function, liveRangeBits);

			requiredSize = getRequiredInterferenceGraphSize(function);
			if (interferenceBitsSize < requiredSize) {
				free(interferenceBits);
				interferenceBitsSize = my_max(requiredSize, interferenceBitsSize * 2);

				interferenceBits = static_cast<u64 *>(malloc(interferenceBitsSize * sizeof(u64)));
			}

			calculateInterferenceGraph(function, interferenceBits, liveRangeBits);

			if (optimizationSettings.coalesceRegisters) {
				while (coalesceRegisters(function, interferenceBits)); // @Audit Make sure that register coalescing doesn't coalesce arguments when it shouldn't

				removeNoops(function);
			}


			allocateRegisters(function, compiler.argCount, interferenceBits);

			removeNoops(function);
			canonize(function);
#if 0
			if (function->flags & DECL_IS_LOCAL) {
				irOutput << getFilename(function->startLocation.fileUid) << '$';
			}

			irOutput << function->name << std::endl;

			for (u32 i = 0; i < function->ops.size(); i++) {
				Ir &op = function->ops[i];

				if (op.flags & IR_IS_LEADER)
					irOutput << std::endl;

				irOutput << i << ": " << irTypeNames[static_cast<u8>(op.type)];

				if (op.dest) {
					printReg(op.dest);
					irOutput << " <-";
				}

				for (u32 j = 0; j < op.regCount; j++) {
					if (op.type == IrType::CALL) {
						printReg(op.callRegs[j]);

						printConstraints(op.callRegs[j], constraints + i * (function->largestReg + 1));
					}
					else {
						printReg(op.regs[j]);

						printConstraints(op.regs[j], constraints + i * (function->largestReg + 1));
					}
				}

				switch (op.type) {
					case IrType::IF_Z:
					case IrType::IF_NZ:
					case IrType::IF_EQ:
					case IrType::IF_NEQ:
					case IrType::IF_G:
					case IrType::IF_LE:
					case IrType::IF_L:
					case IrType::IF_GE:
					case IrType::IF_A:
					case IrType::IF_BE:
					case IrType::IF_B:
					case IrType::IF_AE:
						irOutput << " GOTO " << op.jumpTarget;
						break;
					case IrType::GOTO:
						irOutput << ' ' << op.jumpTarget;
						break;
				}

				irOutput << std::endl;
			}
			irOutput << std::endl;

#endif
		}


		codeGenQueue.add(function);

	}

error:
	// Signal the code generator thread that we're done
	codeGenQueue.add(nullptr);
}
