#pragma once

#include "Basic.h"
#include "String.h"
#include "BucketedArenaAllocator.h"

#define IR_TYPE \
	definer(INVALID), \
\
	definer(NOOP), \
	definer(IF_Z), \
	definer(IF_NZ), \
	definer(IF_EQ), \
	definer(IF_NEQ), \
	definer(IF_L), \
	definer(IF_LE), \
	definer(IF_G), \
	definer(IF_GE), \
	definer(IF_A), \
	definer(IF_AE), \
	definer(IF_B), \
	definer(IF_BE), \
	definer(IF_AND_Z), \
	definer(IF_AND_NZ), \
	definer(GOTO), \
	definer(AND), \
	definer(OR), \
	definer(XOR), \
	definer(EQ), \
	definer(NOT_EQ), \
	definer(NOT), \
	definer(ABOVE), \
	definer(ABOVE_EQUAL), \
	definer(BELOW), \
	definer(BELOW_EQUAL), \
	definer(GREATER), \
	definer(GREATER_EQUAL), \
	definer(LESS), \
	definer(LESS_EQUAL), \
	definer(ADD), \
	definer(SUB), \
	definer(NEG), \
	definer(MUL), \
	definer(DIV), \
	definer(MOD), \
	definer(LSHIFT), \
	definer(RSHIFT), \
	definer(ARSHIFT), \
	definer(ARRAY), \
	definer(SET), \
	definer(RETURN), \
	definer(CALL), \
	definer(READ), \
	definer(WRITE)

#define AST_TYPE \
	definer(INVALID), \
		\
	definer(ARGUMENT_DECL),\
	definer(VAR_DECL),\
\
	definer(UNRESOLVED_GLOBAL),\
	definer(UNRESOLVED_GLOBAL_VAR_ADDRESS), /* An unresolved global that must be a variable not an array or function */\
\
	definer(LOCAL_VAR),\
	/*definer(GLOBAL_VAR),*/ /* Any access to a var will be replaced with DEREF(GLOBAL_POINTER) */ \
	definer(GLOBAL_POINTER),\
		\
	definer(NOOP),\
		\
	definer(LOOP),\
	definer(BREAK),\
	definer(CONTINUE),\
		\
	definer(IF_ELSE),\
		\
	definer(TERNARY),\
\
	definer(RETURN),\
		\
	definer(L_AND),\
	definer(L_OR),\
		\
	definer(SEQUENCE),\
		\
	definer(NEG),\
	definer(BIT_NOT),\
	definer(DEREF),\
	definer(ADROF),\
		\
	definer(ADD),\
	definer(SUB),\
	definer(MUL),\
	definer(DIV),\
	definer(MOD),\
		\
	definer(EQUAL),\
	definer(GREATER),\
	definer(LESS),\
	definer(UGREATER),\
	definer(ULESS),\
		\
	definer(LSHIFT),\
	definer(RSHIFT),\
	definer(URSHIFT),\
		\
		\
	definer(BIT_AND),\
	definer(BIT_OR),\
	definer(XOR),\
		\
	definer(CALL),\
		\
	definer(ARRAY),\
		\
	definer(INT_LITERAL),\
		\
	definer(ASSIGN),\
		\
	definer(MAX)\

#define definer(x) x

enum class AstType : u8 {
	AST_TYPE
};

enum class IrType : u8 {
	IR_TYPE
};

#undef definer
#define definer(x) #x

inline const char *astTypeNames[] = {
	AST_TYPE
};

inline const char *irTypeNames[] = {
	IR_TYPE
};

#undef definer
#undef AST_TYPE

#define AST_IS_TREE 0x1
#define AST_VAR_HAS_REGISTER_ASSIGNED 0x2

#define AST_UNRESOLVED_IDENTIFIER_HAS_BEEN_REPORTED 0x4
#define AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN 0x8
#define AST_UNRESOLVED_WAITING_ON_VALUE 0x10

#define AST_LOCAL_VAR_IS_DEREF_ITERATOR 0x20

#define DECL_IS_EXTERN 0x1
#define DECL_IS_LOCAL 0x2

#define DECL_HAS_EXPRS 0x4

#define DECL_HAS_BEEN_WRITTEN_TO_BINARY 0x8

#define DECL_FUNCTION_RETURN_TYPE_IS_KNOWN 0x10
#define DECL_FUNCTION_IS_VOID 0x20

#define DECL_CIRCULAR_DEPENDENCY_HAS_BEEN_REPORTED 0x40

enum class RegType : u8 {
#if BUILD_DEBUG
	INVALID,  // In fast builds we want NONE to be zero so if checks on it can be lightning fast
#endif
	NONE, 
	REGISTER, 
	STATIC_ADROF, 
	IMMEDIATE
};

struct Reg {
	struct Decl *decl;
	union {
		ulang unumber;
		slang number;
	};
#ifdef BUILD_DEBUG
	RegType type = RegType::INVALID;
#else
	RegType type;
#endif

	inline operator bool() const { return type != RegType::NONE; }

	inline bool operator==(const Reg &other) const {
		if (other.type != type) return false;

		switch (type) {
			case RegType::REGISTER:
				return unumber == other.unumber;
			case RegType::STATIC_ADROF:
				return number == other.number && decl == other.decl;
			case RegType::IMMEDIATE:
				return number == other.number;
			default:
				return true;
		}
	}
	
	inline bool operator!=(const Reg &other) const { return !operator==(other); }
};

#define IR_IS_LEADER 0x1
#define IR_IS_JUMP_TARGET 0x2
#define IR_IS_MULTIPLE_JUMP_TARGET 0x4
#define IR_IS_IN_LOOP 0x8

struct Ir {
	union {
		Reg regs[2];
		Array<Reg> callRegs;
	};
	Reg dest = { nullptr, 0, RegType::NONE };

	u32 jumpTarget;
	ulang regCount = 0;
	u8 flags;
	
#ifdef BUILD_DEBUG
	IrType type = IrType::INVALID;
#else
	IrType type;
#endif
};

enum class DeclType : u8 {
	INVALID, 
	FUNCTION,
	VAR,
	ARRAY,
	STRING, 
	CONST, 
	MAX
};

struct Decl {
	String name;

	Array<ulang> relocations;

	CodeLocation startLocation;
	EndLocation endLocation;

	ulang locationInBinary;

#ifdef BUILD_DEBUG
	DeclType type = DeclType::INVALID;
#else
	DeclType type;
#endif
	u8 flags = 0;

	Decl(DeclType type) : type(type) {}
};

struct AstNode {
	CodeLocation startLocation;
	EndLocation endLocation;
	u8 flags = 0;

#ifdef BUILD_DEBUG
	AstType type = AstType::INVALID;
#else
	AstType type;
#endif

#ifdef BUILD_DEBUG
	virtual ~AstNode() {} // Give it a vtable so the debugger can tell what node type it is and I don't have to cast to view it 
#endif
};

struct AstLeafNode : AstNode {
	String text;

	union {
		AstLeafNode *localIdent;
		Decl *globalIdent;
	};
	union {
		slang number;
		ulang unumber;
	};

	AstLeafNode() : text() {};
};

struct AstTreeNode : AstNode {
	// @Improvement, maybe make sequences, add, sub, etc. just use 2 ops and layer them, then we can use a fixed size array of three nodes (3 for if-else)
	SmallArray<AstNode *, 2> children;

	AstTreeNode() { flags |= AST_IS_TREE; }
};


struct DeclWithExpr : Decl {
	BucketedArenaAllocator astNodeAllocator;
	Array<AstLeafNode *> unresolvedIdentifiers;

	DeclWithExpr(DeclType type) : Decl(type), astNodeAllocator(2048) { flags |= DECL_HAS_EXPRS; }

	inline AstTreeNode *allocTreeNode() {
		constexpr u32 size = static_cast<u32>(my_max(sizeof(AstLeafNode), sizeof(AstTreeNode)));

		AstTreeNode *memory = static_cast<AstTreeNode *>(astNodeAllocator.allocate(size));

		new (memory) AstTreeNode;

		return memory;
	}

	inline AstLeafNode *allocLeafNode() {
		constexpr u32 size = static_cast<u32>(my_max(sizeof(AstLeafNode), sizeof(AstTreeNode)));

		AstLeafNode *memory = static_cast<AstLeafNode *>(astNodeAllocator.allocate(size));

		new (memory) AstLeafNode;

		return memory;
	}

	// The leaf's name had better be freed if it had one by this point
	inline AstTreeNode *convertToTreeNode(AstLeafNode *leaf) {
		AstTreeNode *tree = reinterpret_cast<AstTreeNode *>(leaf); // @Volatile, this relies on the fact that all ast nodes are allocated the same size by our allocator

		tree->flags |= AST_IS_TREE;
		new (&tree->children) decltype(tree->children); // Initialize the child array

		return tree;
	}

	// The tree's children had better be freed
	inline AstLeafNode *convertToLeafNode(AstTreeNode *tree) {
		AstLeafNode *leaf = reinterpret_cast<AstLeafNode *>(tree); // @Volatile, this relies on the fact that all ast nodes are allocated the same size by our allocator

		leaf->flags &= ~AST_IS_TREE;
		new (&leaf->text) String;

		return leaf;
	}
};

struct DeclFunction : DeclWithExpr {
	Array<AstLeafNode *> arguments;
	AstNode *body;

	Array<Ir> ops;

	ulang *shuffle;
	ulang shuffleCount;
	ulang largestReg;


	DeclFunction() : DeclWithExpr(DeclType::FUNCTION) {}
};

struct DeclVar : DeclWithExpr {
	AstNode *value;

	DeclVar() : DeclWithExpr(DeclType::VAR) {}
};

struct DeclArray : DeclWithExpr {
	union {
		slang *values;
		AstNode **exprs;
	};
	AstNode *exprCount;
	ulang count;

	DeclArray() : DeclWithExpr(DeclType::ARRAY) {}
};

struct DeclString : Decl {
	DeclString *parent = nullptr;

	DeclString() : Decl(DeclType::STRING) {}
};