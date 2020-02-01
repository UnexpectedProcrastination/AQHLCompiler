#pragma once

#include "Basic.h"
#include "Array.h"
#include "Ast.h"

extern u32 maxBracktrackCountForComplexConstraints;

extern Array<const char *> buildFiles;
extern std::mutex buildFilesMutex;

extern ulang stackSize;
extern bool outputIr;
extern bool outputSymbols;

extern bool doColorPrint;

extern char *output;
extern std::ofstream symbolOutput;
extern std::ofstream irOutput;

extern volatile bool hadErrors;

extern bool fileMap;

#define READ_BUFFER_SIZE 1024

enum class TokenT : u8 {
	UNINITIALIZED,
	END_OF_FILE,
	SYMBOL,
	INT_LITERAL,
	STRING_LITERAL,
	KEYWORD,
	IDENTIFIER,
	LOCAL_VAR, // Resolve local identifiers during lexing so we don't have to allocate space for the identifier to do a lookup later
	INVALID_CHAR
};

struct Token {
	union {
		String text;
		slang value;
		char c;
		AstLeafNode *localVar;
	};

	TokenT type;

	Token() : type(TokenT::UNINITIALIZED) {}

	Token(TokenT type, char c, [[maybe_unused]] char dummy) : type(type), c(c) {};
	Token(TokenT type, String text) : type(type), text(text) {};
	Token(TokenT type, slang value) : type(type), value(value) {};
	Token(AstLeafNode *localVar) : type(TokenT::LOCAL_VAR), localVar(localVar) {};

	inline bool Token::operator==(const Token &other) {
		if (other.type != type)
			return false;

		switch (type) {
			case TokenT::END_OF_FILE:
				return true;
			case TokenT::KEYWORD:
			case TokenT::SYMBOL:
				return text.characters == other.text.characters;
			case TokenT::STRING_LITERAL:
			case TokenT::IDENTIFIER:
				return text == other.text;
			case TokenT::INT_LITERAL:
				return value == other.value;
			case TokenT::INVALID_CHAR:
				return c == other.c;
			case TokenT::LOCAL_VAR:
				return localVar == other.localVar;
			default:
				return false;
		}
	}

	inline bool operator!=(const Token &other) {
		return !(*this == other);
	}
};

struct LexerState {
	CodeLocation tokenStartLocation;
	CodeLocation location;
	HANDLE handle; // @Platform

	Token lastToken;

	char undo = 0;
	CodeLocation undoLocation;

	String_Hasher hasher;
	DeclWithExpr *currentDecl = nullptr;
	DeclFunction *currentFunction = nullptr;
	Array<Array<AstLeafNode *>> localScopeStack;
	Array<AstNode *> forIncrementStack;
	u32 currentScopeStackDepth = 0;


	u32 readIndex = 0;
	u32 readLimit = 0;
	bool lastFileReadWasNotFull = false;
	char readBuffer[READ_BUFFER_SIZE];
};

#define msg(x) ((new std::string((std::ostringstream() << x).str()))->c_str())

#define WARNING_ARRAY_ALLOCATION_IN_LOOP 1
#define WARNING_ZERO_SIZE_ARRAY_INITIALIZER 2
#define WARNING_INITIALIZER_WRONG_SIZE 3
#define WARNING_ZERO_SIZE_ARRAY 4

void reportError(const CodeLocation &startLocation, const EndLocation &endLocation, const char *message, const char *type = "Error");
void reportError(const LexerState *state, const char *message, const char *type = "Error");
void reportError(const CodeLocation &location, const char *message, const char *type = "Error");
void reportError(const Decl *location, const char *message, const char *type = "Error");
void reportError(const AstNode *location, const char *message, const char *type = "Error");
void reportError(const char *message, const char *type = "Error");

void reportWarning(u64 id, Decl *location, const char *message, const char *type = "Warning");
void reportWarning(u64 id, AstNode *location, const char *message, const char *type = "Warning");

bool addBuildFileFromLoad(const char *file, CodeLocation startLocation, EndLocation endLocation);

struct OptimizationSettings {
	bool advancedOptimizations;

	bool deleteRedundantBranches;
	bool advancedThreadJumps;
	bool comboCompareJumps;
	bool redundantStoreElimination;
	bool propagateConstants;
	bool simplifyConstantExpressions;
	bool copyElision;
	bool moveStatementToUse;
	bool useConstraints;

	bool renameRegisters;
	bool coalesceRegisters;
	bool allocateRegisters;

	bool usesAccessInfo;

	bool optimizeFramePointers;
	bool stringPacking;

	bool deduplicate;

	OptimizationSettings();

	void enableO1();

	void enableO2();
};

extern OptimizationSettings optimizationSettings;

void completeFile();