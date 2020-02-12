#include "Basic.h"
#include "Resolver.h"

#include "Array.h"
#include "String.h"
#include "ArraySet.h"
#include "CodeGenerator.h"
#include "Parser.h"
#include "Optimizer.h"
#include "CompilerMain.h"

struct Dependency {
	String name;
	Array<DeclWithExpr *> decls;
};

WorkQueue<Decl *> resolverQueue;
static Array<Decl *> globals;
static Array<Array<Decl *>> locals;
static Array<Dependency> dependencies;

void resetResolver() {
	for (auto it : globals) delete it;
	globals.clear();

	for (auto &it : locals) {
		for (auto i : it) {
			delete i;
		}

		it.clear();
	}

	locals.clear();
}

static bool doResolve(DeclWithExpr *decl, AstLeafNode *unresolved, Decl *resolve, bool *ready) {
	if (resolve->type == DeclType::VAR) {
		if (unresolved->type == AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS) {

			assert(decl->type == DeclType::FUNCTION); // We shouldn't be taking an address anywhere but a function

			unresolved->type = AstType::GLOBAL_POINTER;
			unresolved->globalIdent = resolve;
		}
		else {
			assert(unresolved->type == AstType::UNRESOLVED_GLOBAL);

			if (decl->type == DeclType::FUNCTION) {
				AstTreeNode *deref = decl->convertToTreeNode(unresolved);
				deref->type = AstType::DEREF;

				// It is safe to access the arena allocator on a different thread since by the time a function has been passed to the resolver we are done with parsing
				unresolved = decl->allocLeafNode();
				unresolved->type = AstType::GLOBAL_POINTER;
				unresolved->startLocation = deref->startLocation;
				unresolved->endLocation = deref->endLocation;
				unresolved->globalIdent = resolve;

				deref->children.add(unresolved);
			}
			else {
				assert(decl->type == DeclType::VAR || decl->type == DeclType::CONST || decl->type == DeclType::ARRAY);

				DeclVar *var = static_cast<DeclVar *>(resolve);

				if (var->value->type == AstType::INT_LITERAL) {
					unresolved->flags &= ~AST_UNRESOLVED_WAITING_ON_VALUE;
					unresolved->type = AstType::INT_LITERAL;
					unresolved->number = static_cast<AstLeafNode *>(var->value)->number;
				}
				else {
					unresolved->flags |= AST_UNRESOLVED_WAITING_ON_VALUE;
					unresolved->globalIdent = resolve;
					*ready = false;
					return false;
				}
			}
		}

		unresolved->text.free();
	}
	else if (resolve->type == DeclType::CONST) {
		if (unresolved->type == AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS) {
			const char *err;
			if (unresolved->flags & AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN) {
				err = msg("Cannot assign to " << unresolved->text << " it is a constant");
			}
			else {
				err = msg("Cannot take the address of " << unresolved->text << " it is a constant so has no storage");
			}

			reportError(unresolved, err);
			return false;
		}
		else {
			assert(unresolved->type == AstType::UNRESOLVED_GLOBAL);

			if (resolve->flags & DECL_IS_EXTERN) {

				if (decl->type == DeclType::FUNCTION) {
					unresolved->type = AstType::GLOBAL_POINTER;
					unresolved->globalIdent = resolve;
				}
				else {
					reportError(unresolved, msg("Cannot use " << unresolved->text << " at compile time, it is extern"));
				}
			}
			else {
				DeclVar *const_ = static_cast<DeclVar *>(resolve);

				if (const_->value->type == AstType::INT_LITERAL) {
					assert(const_->value->type == AstType::INT_LITERAL);

					unresolved->flags &= ~AST_UNRESOLVED_WAITING_ON_VALUE;

					unresolved->type = AstType::INT_LITERAL;
					unresolved->number = static_cast<AstLeafNode *>(const_->value)->number;
				}
				else {
					unresolved->flags |= AST_UNRESOLVED_WAITING_ON_VALUE;
					unresolved->globalIdent = resolve;
					*ready = false;
					return false;
				}
			}

			unresolved->text.free();
		}
	}
	else {
		if (unresolved->type == AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS) {
			std::ostringstream ss;

			const char *type;

			switch (resolve->type) {
				case DeclType::FUNCTION:
					type = "a function";
					break;
				case DeclType::ARRAY:
					type = "an array";
					break;
				case DeclType::STRING:
					type = "a string";
					break;
				default:
					type = "internal compiler error: unknown type";
					break;
			}

			const char *err;

			if (unresolved->flags & AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN) {
				err = msg("Cannot assign to " << unresolved->text << " it is " << type);
			}
			else {
				err = msg("Cannot take the address of " << unresolved->text << " it is " << type << " so is already an address");
			}

			reportError(unresolved, err);
			return false;
		}
		else {
			assert(unresolved->type == AstType::UNRESOLVED_GLOBAL);

			if (decl->type == DeclType::FUNCTION) {
				unresolved->type = AstType::GLOBAL_POINTER;
				unresolved->globalIdent = resolve;
			}
			else {
				std::ostringstream ss;

				const char *type;

				switch (resolve->type) {
					case DeclType::FUNCTION:
						type = "a function";
						break;
					case DeclType::ARRAY:
						type = "an array";
						break;
					case DeclType::STRING:
						type = "a string";
						break;
					default:
						type = "internal compiler error: unknown type";
						break;
				}

				reportError(unresolved, msg("Cannot reference " << unresolved->text << " at compile time it is " << type));
				return false;
			}

			unresolved->text.free();
		}
	}

	return true;
}

// Division rounding is poorly defined for negative numbers in C++
static slang divide(slang a, slang b) {
	slang val = (a < 0 ? -a : a) / (b < 0 ? -b : b);

	return (a ^ b) < 0 ? -val : val;
}

static void evaluateVar(DeclWithExpr *decl, AstNode *value) {
	AstLeafNode *leaf = static_cast<AstLeafNode *>(value);
	AstTreeNode *tree = static_cast<AstTreeNode *>(value);

	if (value->flags & AST_IS_TREE) {
		for (auto child : tree->children) {
			evaluateVar(decl, child);

			assert(child->type == AstType::INT_LITERAL);
		}

		auto &nums = static_cast<SmallArray<AstLeafNode *, 2>>(tree->children);

		slang result;

		switch (tree->type) {
			case AstType::ADD: {
				result = 0;

				for (auto num : nums) result += num->number;
				break;
			}
			case AstType::SUB: {
				result = nums[0]->number;

				for (u32 i = 1; i < nums.size(); i++) result -= nums[i]->number;
				break;
			}
			case AstType::MUL: {
				result = 1;

				for (auto num : nums) result *= num->number;
				break;
			}
			case AstType::XOR: {
				result = 0;

				for (auto num : nums) result ^= num->number;
				break;
			}
			case AstType::BIT_AND: {
				result = static_cast<slang>(ULANG_MAX);

				for (auto num : nums) result &= num->number;
				break;
			}
			case AstType::BIT_OR: {
				result = 0;

				for (auto num : nums) result |= num->number;
				break;
			}
			case AstType::DIV: {
				result = divide(nums[0]->number, nums[1]->number);

				break;
			}
			case AstType::MOD: {
				result = nums[0]->number - (divide(nums[0]->number, nums[1]->number) * nums[1]->number); // Perform mod so that x % y == x - x / y * y, C++ doesn't define divide/mod well for negative numbers so do it manually

				break;
			}
			case AstType::L_AND: {
				result = nums[0]->number;

				for (u32 i = 1; i < nums.size() && result; i++) {
					result = nums[i]->number;
				}

				break;
			}
			case AstType::L_OR: {
				result = nums[0]->number;

				for (u32 i = 1; i < nums.size() && !result; i++) {
					result = nums[i]->number;
				}

				break;
			}
			case AstType::TERNARY: {
				result = nums[0]->number ? nums[1]->number : nums[2]->number;

				break;
			}
			case AstType::NEG: {
				result = -nums[0]->number;
				
				break;
			}
			case AstType::BIT_NOT: {
				result = ~nums[0]->number;

				break;
			}
			case AstType::LSHIFT: {
				result = nums[0]->number << (nums[1]->unumber % BITS_IN_LANG_SIZE);

				break;
			}
			case AstType::RSHIFT: {
				result = nums[0]->number >> (nums[1]->unumber % BITS_IN_LANG_SIZE);

				break;
			}
			case AstType::URSHIFT: {
				result = static_cast<slang>(nums[0]->unumber << (nums[1]->unumber % BITS_IN_LANG_SIZE));

				break;
			}
			case AstType::EQUAL: {
				result = nums[0]->number == nums[1]->number ? 1 : 0;
				
				break;
			}
			case AstType::LESS: {
				result = nums[0]->number < nums[1]->number ? 1 : 0;

				break;
			}
			case AstType::GREATER: {
				result = nums[0]->number > nums[1]->number ? 1 : 0;

				break;
			}
			case AstType::ULESS: {
				result = nums[0]->unumber < nums[1]->unumber ? 1 : 0;

				break;
			}
			case AstType::UGREATER: {
				result = nums[0]->unumber > nums[1]->unumber ? 1 : 0;

				break;
			}
			default:
				assert(false);
		}

		tree->children.free();

		leaf = decl->convertToLeafNode(tree);
		leaf->type = AstType::INT_LITERAL;
		leaf->number = result;
	}
}

static bool resolveAgainstNewDeclaration(Decl *declaration);

static bool finishResolving(DeclWithExpr *decl) {
	if (!decl->unresolvedIdentifiers.size()) {
		decl->unresolvedIdentifiers.free();

		if (decl->type == DeclType::FUNCTION) {
			// Add to the optimizer queue
			optimizerQueue.add(static_cast<DeclFunction *>(decl));
		}
		else if (decl->type == DeclType::VAR || decl->type == DeclType::CONST) {
			auto var = static_cast<DeclVar *>(decl);
			evaluateVar(var, var->value);

			assert(var->value->type == AstType::INT_LITERAL);
			AstLeafNode *newNode = new AstLeafNode;
			*newNode = *static_cast<AstLeafNode *>(var->value);
			var->astNodeAllocator.free();
			var->value = newNode;

			if (decl->type != DeclType::CONST)
				codeGenQueue.add(decl);
			resolveAgainstNewDeclaration(decl);
		}
		else if (decl->type == DeclType::ARRAY) {
			auto arr = static_cast<DeclArray *>(decl);

			ulang count = arr->count;

			if (arr->exprCount) {
				evaluateVar(arr, arr->exprCount);
				assert(arr->exprCount->type == AstType::INT_LITERAL);

				count = static_cast<AstLeafNode *>(arr->exprCount)->unumber;
				
				if (arr->exprs) {
					if (arr->count < count) {
						reportWarning(WARNING_INITIALIZER_WRONG_SIZE, arr, msg("Shorter initializer given than length of array, remaining values will initialize to zero, initializer length was " << arr->count << " and array length is " << count));
					}
					else if (arr->count > count) {
						reportError(arr, msg("Array initializer was too long, initializer length was " << arr->count << ", but array length is " << count));
						return false;
					}
				}
			}

			assert(count >= arr->count);

			slang *values = static_cast<slang *>(malloc(sizeof(slang) * count));

			if (arr->exprs) {
				for (ulang i = 0; i < arr->count; i++) {
					evaluateVar(arr, arr->exprs[i]);
					assert(arr->exprs[i]->type == AstType::INT_LITERAL);

					values[i] = static_cast<AstLeafNode *>(arr->exprs[i])->number;
				}

				arr->astNodeAllocator.free();
				free(arr->exprs);
			}

			for (ulang i = arr->count; i < count; i++) {
				values[i] = 0;
			}

			arr->count = count;
			arr->values = values;
			codeGenQueue.add(arr);
		}
		else {
			assert(false);
		}
	}

	return true;
}

static bool resolveAgainstNewDeclaration(Decl *declaration) {
	Dependency *dependency = nullptr;

	for (u32 i = 0; i < dependencies.size(); i++) {
		if (dependencies[i].name == declaration->name) {
			dependency = &dependencies[i];
			break;
		}
	}

	if (dependency) {
		for (u32 i = 0; i < dependency->decls.size(); i++) {
			auto decl = dependency->decls[i];

			for (u32 j = 0; j < decl->unresolvedIdentifiers.size(); j++) {
				AstLeafNode *unresolved = decl->unresolvedIdentifiers[j];

				if ((unresolved->flags & AST_UNRESOLVED_WAITING_ON_VALUE) ? // If we have already determined which identifier we refer to but it is a const we hadn't got the value of yet
					(declaration == unresolved->globalIdent) : // Make sure we are the decl they were resolving against
					(unresolved->text == declaration->name && // Otherwise, make sure this unresolved identifier is the one that we're looking for
					(!(declaration->flags & DECL_IS_LOCAL) || // If the declaration we are processing is global
						declaration->startLocation.fileUid == decl->startLocation.fileUid))) { // or is local and in the same file as the depending function we resolve

					bool ready = true;

					if (doResolve(decl, unresolved, declaration, &ready)) {
						decl->unresolvedIdentifiers.unordered_remove(j--);
						dependency->decls.unordered_remove(i--); // It may be better to do an orderer remove for cache reasons so that we continue resolving identifiers for the same function



						if (!dependency->decls.size()) {
							dependency->decls.free();
							dependency->name.free();
							dependencies.unordered_remove(dependency);
						}

						break; // Only resolve one usage per loop so that we don't have to search through dependency->functions to find the correct index to remove each time, we will come back and resolve the other identifiers again in the outer loop since the function is stored in dependency->functions once for each usage
					}
					else {
						if (ready) {
							return false;
						}
						else {
							continue;
						}
					}
				}
			}

			if (!finishResolving(decl)) return false;
		}
	}

	return true;
}

static s64 findLoop(Array<DeclWithExpr *> &loop, DeclWithExpr *decl) {
	loop.add(decl);

	for (auto &unresolved : decl->unresolvedIdentifiers) {
		if (unresolved->flags & AST_UNRESOLVED_WAITING_ON_VALUE) {
			assert(unresolved->globalIdent->flags & DECL_HAS_EXPRS);

			for (u32 i = 0; i < loop.size(); i++) {
				if (loop[i] == unresolved->globalIdent) {
					return i;
				}
			}

			s64 loopIndex = findLoop(loop, static_cast<DeclWithExpr *>(unresolved->globalIdent));

			if (loopIndex != -1) {
				return loopIndex;
			}
		}
	}

	loop.pop();

	return -1;
}

static bool reportCircularDependencies(Array<DeclWithExpr *> &loop, DeclWithExpr *decl) {
	loop.clear();

	s64 loopIndex = findLoop(loop, decl);

	if (loopIndex != -1) {
		for (u32 i = static_cast<u32>(loopIndex); i < loop.size(); i++) {
			if (loop[i]->flags & DECL_CIRCULAR_DEPENDENCY_HAS_BEEN_REPORTED) return true;
		}

		reportError("There were circular dependencies");

		if (loopIndex + 1 == loop.size()) {
			reportError(loop[loopIndex], msg("The value of " << loop[loopIndex]->name << " depends on itself"), nullptr);
			loop[loopIndex]->flags |= DECL_CIRCULAR_DEPENDENCY_HAS_BEEN_REPORTED;
		}
		else {
			for (u32 i = static_cast<u32>(loopIndex); i < loop.size(); i++) {
				reportError(loop[i], msg("The value of " << loop[i]->name << " depends on " << loop[i + 1 == loop.size() ? static_cast<u32>(loopIndex) : i + 1]->name), nullptr);
				loop[i]->flags |= DECL_CIRCULAR_DEPENDENCY_HAS_BEEN_REPORTED;
			}
		}

		return true;
	}

	return false;
}

void runResolver() {
	PROFILE_FUNC();

	u32 completed = 0;

	while (true) {
		Decl *declaration = resolverQueue.take();



		if (!declaration) {
			if (++completed == NUM_PARSER_THREADS) {
				break;
			}
			else {
				continue;
			}
		}


		while (declaration->startLocation.fileUid >= locals.size()) locals.add();

		// @Improvement maybe defer this check until after we resolve dependencies, since if this check fails we stop compilation
		// so the incorrect resolution doesn't matter. This will only improve startup/drainout as this pipeline section will have
		// less latency but the same throughput :DeferredChecks
		// Alternatively we could actually move this check onto a separate thread for further parallelism to actually improve throughput, 
		// however this is not currently the bottleneck for compilation so don't bother with that complexity
		if (declaration->flags & DECL_IS_LOCAL) {
			for (Decl *global : globals) {
				if (global->name == declaration->name) {					
					reportError(declaration, msg(declaration->name << " is already defined at " << global->startLocation));
					goto error;
				}
			}

			for (Decl *local : locals[declaration->startLocation.fileUid]) {
				if (local->name == declaration->name) {
					reportError(declaration, msg(declaration->name << " is already defined at " << local->startLocation));
					goto error;
				}
			}

			locals[declaration->startLocation.fileUid].add(declaration);
		}
		else {
			for (Decl *global : globals) {
				if (global->name == declaration->name) {
					reportError(declaration, msg(declaration->name << " is already defined at " << global->startLocation));
					goto error;
				}
			}

			// Make sure the variable isn't defined in any local scopes
			for (const auto &file : locals) {
				for (Decl *local : file) {
					if (local->name == declaration->name) {
						reportError(declaration, msg(declaration->name << " is already defined at " << local->startLocation));
						goto error;
					}
				}
			}

			globals.add(declaration);
		}

		if ((declaration->flags & DECL_IS_EXTERN) && declaration->type != DeclType::ARRAY) { // Extern arrays need to go through resolving since the array length may need to be resolved
			codeGenQueue.add(declaration);
		}
		else {
			assert(declaration->flags & DECL_HAS_EXPRS);

			DeclWithExpr *decl = static_cast<DeclWithExpr *>(declaration);

			for (u32 i = 0; i < decl->unresolvedIdentifiers.size(); i++) {
				AstLeafNode *unresolved = decl->unresolvedIdentifiers[i];

				Decl *resolve = nullptr;

				for (Decl *global : globals) {
					if (global->name == unresolved->text) {
						resolve = global;
						break;
					}
				}

				if (!resolve) {
					for (Decl *local : locals[decl->startLocation.fileUid]) {
						if (local->name == unresolved->text) {
							resolve = local;
							break;
						}
					}
				}

				bool ready = true;

				if (resolve) {
					if (doResolve(decl, unresolved, resolve, &ready)) {
						decl->unresolvedIdentifiers.unordered_remove(i--);
					}
					else {
						if (ready) {
							goto error;
						}
						else {
							continue;
						}
					}
				}
			}

			if (decl->unresolvedIdentifiers.size()) {
				for (AstLeafNode *unresolved : decl->unresolvedIdentifiers) {
					bool found = false;

					for (Dependency &dependency : dependencies) {
						if (dependency.name == unresolved->text) {
							dependency.decls.add(decl);
							found = true;
							break;
						}
					}

					if (!found)
						dependencies.add({ copyString(unresolved->text), {decl} });
				}
			}
			else {
				if (!finishResolving(decl)) goto error;
			}
		}

		if (!resolveAgainstNewDeclaration(declaration)) goto error;
	}



	if (dependencies.size()) {
		if (!hadErrors) {
			Array<DeclWithExpr *> loop;

			for (const auto &dependency : dependencies) {

				for (const auto &failed : dependency.decls) {
					if (!reportCircularDependencies(loop, failed)) {

						for (const auto unresolved : failed->unresolvedIdentifiers) {
							if (!(unresolved->flags & AST_UNRESOLVED_IDENTIFIER_HAS_BEEN_REPORTED) && unresolved->text == dependency.name) {
								unresolved->flags |= AST_UNRESOLVED_IDENTIFIER_HAS_BEEN_REPORTED;

								reportError(unresolved, msg("Could not resolve identifier: " << dependency.name));

								for (const auto &localScope : locals) {
									for (Decl *decl : localScope) {
										if (decl->name == dependency.name) {
											reportError(decl, msg(dependency.name << " is local here. Did you really mean to mark it as local?"), "  ...");
											break;
										}
									}
								}

								break;
							}
						}

					}
				}
			}
		}
	}

	error:
	// Signal the codegen and optimizer threads that we're done
	codeGenQueue.add(nullptr);
	optimizerQueue.add(nullptr);
}
