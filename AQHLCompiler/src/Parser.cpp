#include "Basic.h"
#include "Parser.h"
#include "Array.h"
#include "CompilerMain.h"
#include "Resolver.h"
#include "CodeGenerator.h"

u64 NUM_PARSER_THREADS = 1;

#undef FALSE
#undef TRUE
#undef CONST

bool lexAndParse(const char *filePath, u32 fileUid);
WorkQueue<ParseJob> parserQueue;

void runParser() {
	while (true) {
		ParseJob job = parserQueue.take();

		if (!job.buildFile) {
			parserQueue.add(job); // Let the other threads no to exit
			break;
		}

		bool result = lexAndParse(job.buildFile, job.fileUid);

		if (!result) {
			if (!hadErrors) {
				reportError("Parsing failed but no error was logged", "Internal compiler errror");
			}
			break;
		}

		if (hadErrors) {
			break;
		}
	}

	resolverQueue.add(nullptr);
}

static const Token END_OF_FILE(TokenT::END_OF_FILE, String("<End of file>"));

static const Token IF(TokenT::KEYWORD, String("if"));
static const Token ELSE(TokenT::KEYWORD, String("else"));

static const Token EXTERN(TokenT::KEYWORD, String("extern"));
static const Token LOCAL(TokenT::KEYWORD, String("local"));

static const Token ARRAY(TokenT::KEYWORD, String("array")); // @Cleanup: unify static variables and static arrays in syntax
static const Token FUNCTION(TokenT::KEYWORD, String("function"));
static const Token VAR(TokenT::KEYWORD, String("var"));
static const Token CONST(TokenT::KEYWORD, String("const")); // @Feature,  allow string literals to be defined as consts

static const Token FOR(TokenT::KEYWORD, String("for")); // @Feature: change for loops to look like for i : 0..10, or for short for i: 10, remove c for loops as this for and each should replace 99% of uses, maybe add default iterator names like Jai has
static const Token WHILE(TokenT::KEYWORD, String("while"));
static const Token EACH(TokenT::KEYWORD, String("each")); // @Feature: each i: [array, count] or each i, idx: [array, count] or *i or *i, idx for by pointer
static const Token BREAK(TokenT::KEYWORD, String("break"));
static const Token CONTINUE(TokenT::KEYWORD, String("continue"));

static const Token LOAD(TokenT::KEYWORD, String("#load"));

static const Token RETURN(TokenT::KEYWORD, String("return"));

static const Token OPEN_PAREN(TokenT::SYMBOL, String("("));
static const Token CLOSE_PAREN(TokenT::SYMBOL, String(")"));
static const Token OPEN_SQUARE(TokenT::SYMBOL, String("["));
static const Token CLOSE_SQUARE(TokenT::SYMBOL, String("]"));
static const Token OPEN_CURLY(TokenT::SYMBOL, String("{"));
static const Token CLOSE_CURLY(TokenT::SYMBOL, String("}"));
static const Token COMMA(TokenT::SYMBOL, String(","));
static const Token SEMICOLON(TokenT::SYMBOL, String(";"));

static const Token COLON(TokenT::SYMBOL, String(":"));
static const Token QUESTION(TokenT::SYMBOL, String("?"));

static const Token PLUS(TokenT::SYMBOL, String("+"));
static const Token MINUS(TokenT::SYMBOL, String("-"));
static const Token ASTERISK(TokenT::SYMBOL, String("*"));
static const Token SLASH(TokenT::SYMBOL, String("/"));
static const Token MODULO(TokenT::SYMBOL, String("%"));

static const Token LOGIC_AND(TokenT::SYMBOL, String("&&"));
static const Token LOGIC_OR(TokenT::SYMBOL, String("||"));
static const Token LOGIC_NOT(TokenT::SYMBOL, String("!"));

static const Token BIT_AND(TokenT::SYMBOL, String("&"));
static const Token BIT_OR(TokenT::SYMBOL, String("|"));
static const Token BIT_NOT(TokenT::SYMBOL, String("~"));
static const Token BIT_XOR(TokenT::SYMBOL, String("^"));
static const Token ALSHIFT(TokenT::SYMBOL, String("<<"));
static const Token LSHIFT(TokenT::SYMBOL, String("#>>"));
static const Token ARSHIFT(TokenT::SYMBOL, String(">>"));
static const Token RSHIFT(TokenT::SYMBOL, String("#>>"));

static const Token EQUALITY(TokenT::SYMBOL, String("=="));
static const Token NOT_EQUAL(TokenT::SYMBOL, String("!="));
static const Token LESS(TokenT::SYMBOL, String("<"));
static const Token GREATER(TokenT::SYMBOL, String(">"));
static const Token LESS_OR_EQUAL(TokenT::SYMBOL, String("<="));
static const Token GREATER_OR_EQUAL(TokenT::SYMBOL, String(">="));
static const Token U_LESS(TokenT::SYMBOL, String("#<"));
static const Token U_GREATER(TokenT::SYMBOL, String("#>"));
static const Token U_LESS_OR_EQUAL(TokenT::SYMBOL, String("#<="));
static const Token U_GREATER_OR_EQUAL(TokenT::SYMBOL, String("#>="));

static const Token POUND(TokenT::SYMBOL, String("#"));
static const Token RANGE(TokenT::SYMBOL, String(".."));

static const Token INCREMENT(TokenT::SYMBOL, String("++"));
static const Token DECREMENT(TokenT::SYMBOL, String("--"));

static const Token ASSIGN(TokenT::SYMBOL, String("="));
static const Token PLUS_EQUALS(TokenT::SYMBOL, String("+="));
static const Token MINUS_EQUALS(TokenT::SYMBOL, String("-="));
static const Token TIMES_EQUALS(TokenT::SYMBOL, String("*="));
static const Token DIVIDE_EQUALS(TokenT::SYMBOL, String("/="));
static const Token MODULO_EQUALS(TokenT::SYMBOL, String("%="));
static const Token LSHIFT_EQUALS(TokenT::SYMBOL, String("<<="));
static const Token ALSHIFT_EQUALS(TokenT::SYMBOL, String("#<<="));
static const Token ARSHIFT_EQUALS(TokenT::SYMBOL, String(">>="));
static const Token RSHIFT_EQUALS(TokenT::SYMBOL, String("#>>="));
static const Token BIT_AND_EQUALS(TokenT::SYMBOL, String("&="));
static const Token BIT_OR_EQUALS(TokenT::SYMBOL, String("|="));
static const Token XOR_EQUALS(TokenT::SYMBOL, String("^="));
static const Token LOGIC_AND_EQUALS(TokenT::SYMBOL, String("&&="));
static const Token LOGIC_OR_EQUALS(TokenT::SYMBOL, String("||="));

static const String TRUE_STRING = String("true");
static const String FALSE_STRING = String("false");

static std::ostream &operator<<(std::ostream &out, const Token &token) {
	switch (token.type) {
		case TokenT::END_OF_FILE:
		case TokenT::KEYWORD:
		case TokenT::SYMBOL:
		case TokenT::IDENTIFIER:
			out << token.text;
			break;
		case TokenT::INT_LITERAL:
			out << static_cast<ulang>(token.value); // @Improvement, Flag whether is was decimal, hex, binary, character so we can print the actual value
			break;
		case TokenT::INVALID_CHAR:
			out << token.c;
			break;
		case TokenT::STRING_LITERAL:
			out << '"' << token.text << '"';
			break;
		case TokenT::LOCAL_VAR:
			out << token.localVar->text;
			break;
	}

	return out;
}

static const char *expected(const char *message, const Token &received) {
	return msg(message << ' ' << ", but got " << received << " instead");
}

enum class Lexer : u8 {
	DEFAULT,
	PLUS,
	MINUS,
	SLASH,
	ASTERISK,
	PERCENT,
	AMPERSAND,
	AMPERSAND2,
	PIPE,
	PIPE2,
	CARET,
	EXCLAMATION,
	LESS,
	LESS2,
	GREATER,
	GREATER2,
	EQUALS,
	ZERO,
	STRING,
	STRING_ESCAPE,
	STRING_EMPTY_HEX_ESCAPE,
	STRING_HEX_ESCAPE,
	STRING_DEC_ESCAPE,
	CHAR,
	CHAR_ESCAPE,
	CHAR_EMPTY_HEX_ESCAPE,
	CHAR_HEX_ESCAPE,
	CHAR_DEC_ESCAPE,
	CHAR_END,
	HEX,
	DEC,
	BIN,
	COMMENT,
	MULTI_COMMENT,
	MULTI_COMMENT_END,
	CARRIAGE_RETURN,
	IDENTIFIER,
	POUND,
	POUND_LESS,
	POUND_LESS2,
	POUND_GREATER,
	POUND_GREATER2,
	DOT, 
};

static Array<Token> keywords(16);

void initLexer() {
	keywords.clear();
	keywords.add(IF);
	keywords.add(VAR);
	keywords.add(RETURN);
	keywords.add(FUNCTION);
	keywords.add(ELSE);
	keywords.add(FOR);
	keywords.add(LOCAL);
	keywords.add(WHILE);
	keywords.add(BREAK);
	keywords.add(ARRAY);
	keywords.add(LOAD);
	keywords.add(EXTERN);
	keywords.add(CONTINUE);
	keywords.add(EACH);
	keywords.add(CONST);
}

static char readCharacter(LexerState *state) {
	while (state->readIndex == state->readLimit) { // Use a while loop so we check if that was the last character in the file
		if (state->lastFileReadWasNotFull) {
			return EOF;
		}

		PROFILE_ZONE("ReadFile");
		if (!ReadFile(state->handle, state->readBuffer, READ_BUFFER_SIZE, reinterpret_cast<DWORD *>(&state->readLimit), 0)) { // @Platform
			reportError(state, "Failed to read file", "I/O Error: ");
			return EOF;
		}

		state->lastFileReadWasNotFull = (state->readLimit < READ_BUFFER_SIZE);

		state->readIndex = 0;
	}

	char c = state->readBuffer[state->readIndex++];

	if (c == '\r') {
		if (readCharacter(state) != '\n' && state->readIndex != 0) {
			--state->readIndex;
		}

		return '\n';
	}

	return c;
}

static char readChar(LexerState *state) {
	int c;

	if (state->undo) {
		c = state->undo;
		state->undo = 0;
	}
	else {
		state->undoLocation = state->location;

		c = readCharacter(state);
	}

	if (c == '\n') {
		++state->location.line;
		state->location.column = 1;
	}
	else {
		++state->location.column;
	}

	return (char) c;
}

static void undoReadChar(LexerState *state, char c) {
	assert(!state->undo);

	state->location = state->undoLocation;

	state->undo = c;
}

static bool isValidIdentifierStart(char c) {
	return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

static bool isValidIdentifier(char c) {
	return isValidIdentifierStart(c) || (c >= '0' && c <= '9');
}

static int getEscapeChar(LexerState *state, char c) {
	switch (c) {
		case '"': {
			return '"';
		}
		case 'b': {
			return '\b';
		}
		case 'e': {
			return '\x1b';
		}
		case 'f': {
			return '\f';
		}
		case 'n': {
			return '\n';
		}
		case 'r': {
			return '\r';
		}
		case 't': {
			return 't';
		}
		case 'v': {
			return '\v';
		}
		case '\\': {
			return '\\';
		}
		case '\'': {
			return '\'';
		}
		default: {
			reportError(state->location, msg("Unknown character escape \\" << c));
			return -1;
		}
	}
}


static AstLeafNode *resolveInLocalScope(LexerState *state, const String_Hasher &name);

static Token lexerAdvance(LexerState *state) {
	PROFILE_FUNC();
	Lexer currentState = Lexer::DEFAULT;

	u64 integerValue = 0;

	while (true) {
		if (currentState == Lexer::DEFAULT) {
			state->tokenStartLocation.line = state->location.line;
			state->tokenStartLocation.column = state->location.column;
		}

		char c = readChar(state);
		switch (currentState) {
			case Lexer::DEFAULT: {
				switch (c) {
					case '(':
						return OPEN_PAREN;
					case ')':
						return CLOSE_PAREN;
					case '[':
						return OPEN_SQUARE;
					case ']':
						return CLOSE_SQUARE;
					case '{':
						return OPEN_CURLY;
					case '}':
						return CLOSE_CURLY;
					case ';':
						return SEMICOLON;
					case ',':
						return COMMA;
					case '?':
						return QUESTION;
					case ':':
						return COLON;
					case '~':
						return BIT_NOT;
					case EOF:
						return END_OF_FILE;
					case '+':
						currentState = Lexer::PLUS;
						continue;
					case '-':
						currentState = Lexer::MINUS;
						continue;
					case '/':
						currentState = Lexer::SLASH;
						continue;
					case '*':
						currentState = Lexer::ASTERISK;
						continue;
					case '%':
						currentState = Lexer::PERCENT;
						continue;
					case '&':
						currentState = Lexer::AMPERSAND;
						continue;
					case '|':
						currentState = Lexer::PIPE;
						continue;
					case '^':
						currentState = Lexer::CARET;
						continue;
					case '!':
						currentState = Lexer::EXCLAMATION;
						continue;
					case '<':
						currentState = Lexer::LESS;
						continue;
					case '>':
						currentState = Lexer::GREATER;
						continue;
					case '=':
						currentState = Lexer::EQUALS;
						continue;
					case '0':
						currentState = Lexer::ZERO;
						continue;
					case '"':
						state->hasher.clear();
						currentState = Lexer::STRING;
						continue;
					case '\'':
						currentState = Lexer::CHAR;
						continue;
					case '#':
						currentState = Lexer::POUND;
						continue;
					case '.':
						currentState = Lexer::DOT;
						continue;
					case '\n':
					case '\t':
					case ' ':
					case '\f':
					case '\v':
						continue;
					default:
						if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
							currentState = Lexer::IDENTIFIER;
							state->hasher.clear();
							state->hasher.append(c);
							continue;
						}
						else if (c >= '0' && c <= '9') {
							integerValue = c - '0';
							currentState = Lexer::DEC;
							continue;
						}
						else {
							reportError(state->location, "Invalid character");
							return Token(TokenT::INVALID_CHAR, c, ' ');
						}
				}
				break;
			}
			case Lexer::PLUS: {
				if (c == '+') {
					return INCREMENT;
				}
				else if (c == '=') {
					return PLUS_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return PLUS;
				}
				break;
			}
			case Lexer::DOT: {
				if (c == '.') {
					return RANGE;
				}
				else {
					reportError(state->location, "Cannot have a single .");
					return Token(TokenT::INVALID_CHAR, '.', ' ');
				}
			}
			case Lexer::MINUS: {
				if (c == '-') {
					return DECREMENT;
				}
				else if (c == '=') {
					return MINUS_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return MINUS;
				}
				break;
			}
			case Lexer::SLASH: {
				if (c == '/') {
					currentState = Lexer::COMMENT;
					continue;
				}
				else if (c == '*') {
					currentState = Lexer::MULTI_COMMENT;
					continue;
				}
				else if (c == '=') {
					return DIVIDE_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return SLASH;
				}
				break;
			}
			case Lexer::POUND: {
				if (c == '<') {
					currentState = Lexer::POUND_LESS;
					continue;
				}
				else if (c == '>') {
					currentState = Lexer::POUND_GREATER;
					continue;
				}
				else if (isValidIdentifier(c)) {
					state->hasher.clear();
					state->hasher.append('#');
					state->hasher.append(c);
					currentState = Lexer::IDENTIFIER;
					continue;
				}
				else {
					undoReadChar(state, c);
					return POUND;
				}
				break;
			}
			case Lexer::POUND_LESS: {
				if (c == '=') {
					return U_LESS_OR_EQUAL;
				}
				else if (c == '<') {
					currentState = Lexer::POUND_LESS2;
					continue;
				}
				else {
					undoReadChar(state, c);
					return U_LESS;
				}
				break;
			}
			case Lexer::POUND_LESS2: {
				if (c == '=') {
					return LSHIFT_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return LSHIFT;
				}
				break;
			}
			case Lexer::POUND_GREATER: {
				if (c == '>') {
					currentState = Lexer::POUND_GREATER2;
					continue;
				}
				else if (c == '=') {
					return U_GREATER_OR_EQUAL;
				}
				else {
					undoReadChar(state, c);
					return U_GREATER;
				}
				break;
			}
			case Lexer::POUND_GREATER2: {
				if (c == '=') {
					return RSHIFT_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return RSHIFT;
				}
				break;
			}
			case Lexer::ASTERISK: {
				if (c == '=') {
					return TIMES_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return ASTERISK;
				}
				break;
			}
			case Lexer::PERCENT: {
				if (c == '=') {
					return MODULO_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return MODULO;
				}
				break;
			}
			case Lexer::AMPERSAND: {
				if (c == '=') {
					return BIT_AND_EQUALS;
				}
				else if (c == '&') {
					currentState = Lexer::AMPERSAND2;
					continue;
				}
				else {
					undoReadChar(state, c);
					return BIT_AND;
				}
				break;
			}
			case Lexer::AMPERSAND2: {
				if (c == '=') {
					return LOGIC_AND_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return LOGIC_AND;
				}
			}
			case Lexer::PIPE: {
				if (c == '=') {
					return BIT_OR_EQUALS;;
				}
				else if (c == '|') {
					currentState = Lexer::PIPE2;
					continue;
				}
				else {
					undoReadChar(state, c);
					return BIT_OR;
				}
				break;
			}
			case Lexer::PIPE2: {
				if (c == '=') {
					return LOGIC_OR_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return LOGIC_OR;
				}
			}
			case Lexer::CARET: {
				if (c == '=') {
					return XOR_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return BIT_XOR;
				}
				break;
			}
			case Lexer::EXCLAMATION: {
				if (c == '=') {
					return NOT_EQUAL;
				}
				else {
					undoReadChar(state, c);
					return LOGIC_NOT;
				}
				break;
			}
			case Lexer::LESS: {
				if (c == '<') {
					currentState = Lexer::LESS2;
					continue;
				}
				else if (c == '=') {
					return LESS_OR_EQUAL;
				}
				else {
					undoReadChar(state, c);
					return LESS;
				}
				break;
			}
			case Lexer::LESS2: {
				if (c == '=') {
					return ALSHIFT_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return ALSHIFT;
				}
				break;
			}
			case Lexer::GREATER: {
				if (c == '>') {
					currentState = Lexer::GREATER2;
				}
				else if (c == '=') {
					return GREATER_OR_EQUAL;
				}
				else {
					undoReadChar(state, c);
					return GREATER;
				}
				break;
			}
			case Lexer::GREATER2: {
				if (c == '=') {
					return ARSHIFT_EQUALS;
				}
				else {
					undoReadChar(state, c);
					return ARSHIFT;
				}
				break;
			}
			case Lexer::EQUALS: {
				if (c == '=') {
					return EQUALITY;
				}
				else {
					undoReadChar(state, c);
					return ASSIGN;
				}
				break;
			}
			case Lexer::ZERO: {
				if (c == 'x' || c == 'X') {
					currentState = Lexer::HEX;
					continue;
				}
				else if (c == 'b' || c == 'B') {
					currentState = Lexer::BIN;
					continue;
				}
				else if (c >= '0' && c <= '9') {
					currentState = Lexer::DEC;
					integerValue = c - '0';
					continue;
				}
				else if (c == '_') {
					continue;
				}
				else {
					undoReadChar(state, c);
					return Token(TokenT::INT_LITERAL, 0);
				}
				break;
			}
			case Lexer::STRING: {
				if (c == '"') { // Should we just allow newlines in the middle of a string like we do currently?
					return Token(TokenT::STRING_LITERAL, String(state->hasher));
				}
				else if (c == '\\') {
					currentState = Lexer::STRING_ESCAPE;
					continue;
				}
				else if (c < ' ' || c > '~') {
					reportError(state->location, "Strings must contain only printable characters, use an escape sequence");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}
				else if (c == EOF) {
					reportError(state->location, "Unexpected end of file in the middle of a string");
					return Token(TokenT::INVALID_CHAR, 0, ' ');
				}
				else {
					state->hasher.append(c);
					continue;
				}
				break;
			}
			case Lexer::STRING_ESCAPE: {

				if (c == 'x') {
					currentState = Lexer::STRING_EMPTY_HEX_ESCAPE;
					continue;
				}
				else if (c >= '0' && c <= '9') {
					currentState = Lexer::STRING_DEC_ESCAPE;
					integerValue = c - '0';
					continue;
				}
				else {
					int escape = getEscapeChar(state, c);

					if (escape >= 0) {
						state->hasher.append((char) escape);
						currentState = Lexer::STRING;
						continue;
					}
					else {
						reportError(state->location, "Unexpected end of file in the middle of a string escape");
						return Token(TokenT::INVALID_CHAR, c, ' ');
					}
				}
				break;
			}
			case Lexer::STRING_EMPTY_HEX_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue = c - '0';
					currentState = Lexer::STRING_HEX_ESCAPE;
					continue;
				}
				else if (c >= 'A' && c <= 'F') {
					integerValue = c - 'A' + 10;
					currentState = Lexer::STRING_HEX_ESCAPE;
					continue;
				}
				else if (c >= 'a' && c <= 'f') {
					integerValue = c - 'a' + 10;
					currentState = Lexer::STRING_HEX_ESCAPE;
					continue;
				}
				else {
					reportError(state->location, "Cannot have empty hex escape");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}

				break;
			}
			case Lexer::STRING_HEX_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue *= 16;
					integerValue = c - '0';

					if (integerValue >= 256) {
						integerValue /= 16;
						undoReadChar(state, c);

						state->hasher.append(c);
						undoReadChar(state, c);
						currentState = Lexer::STRING;

					}
					continue;
				}
				else if (c >= 'A' && c <= 'F') {
					integerValue *= 16;
					integerValue = c - 'A' + 10;

					if (integerValue >= 256) {
						integerValue /= 16;
						undoReadChar(state, c);

						state->hasher.append(c);
						undoReadChar(state, c);
						currentState = Lexer::STRING;

					}
					continue;
				}
				else if (c >= 'a' && c <= 'f') {
					integerValue *= 16;
					integerValue = c - 'a' + 10;

					if (integerValue >= 256) {
						integerValue /= 16;
						undoReadChar(state, c);

						state->hasher.append(c);
						undoReadChar(state, c);
						currentState = Lexer::STRING;

					}
					continue;
				}
				else {
					state->hasher.append(c);
					undoReadChar(state, c);
					currentState = Lexer::STRING;
					continue;
				}

				break;
			}
			case Lexer::STRING_DEC_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue *= 10;
					integerValue = c - '0';

					if (integerValue >= 256) {
						integerValue /= 10;
						undoReadChar(state, c);

						state->hasher.append(c);
						undoReadChar(state, c);
						currentState = Lexer::STRING;

					}
					continue;
				}
				else {
					state->hasher.append(c);
					undoReadChar(state, c);
					currentState = Lexer::STRING;
					continue;
				}

				break;
			}
			case Lexer::CHAR_EMPTY_HEX_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue = c - '0';
					currentState = Lexer::CHAR_HEX_ESCAPE;
					continue;
				}
				else if (c >= 'A' && c <= 'F') {
					integerValue = c - 'A' + 10;
					currentState = Lexer::CHAR_HEX_ESCAPE;
					continue;
				}
				else if (c >= 'a' && c <= 'f') {
					integerValue = c - 'a' + 10;
					currentState = Lexer::CHAR_HEX_ESCAPE;
					continue;
				}
				else {
					reportError(state->location, "Cannot have empty hex escape");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}

				break;
			}
			case Lexer::CHAR_HEX_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue *= 16;
					integerValue = c - '0';

					if (integerValue > ULANG_MAX) {
						reportError(state->location, "Character value too large");
						return Token(TokenT::INVALID_CHAR, c, ' ');
					}
					continue;
				}
				else if (c >= 'A' && c <= 'F') {
					integerValue *= 16;
					integerValue = c - 'A' + 10;

					if (integerValue > ULANG_MAX) {
						reportError(state->location, "Character value too large");
						return Token(TokenT::INVALID_CHAR, c, ' ');
					}
					continue;
				}
				else if (c >= 'a' && c <= 'f') {
					integerValue *= 16;
					integerValue = c - 'a' + 10;

					if (integerValue > ULANG_MAX) {
						reportError(state->location, "Character value too large");
						return Token(TokenT::INVALID_CHAR, c, ' ');
					}
					continue;
				}
				else if (c == '\'') {
					return Token(TokenT::INT_LITERAL, static_cast<slang>(integerValue));
				}
				else {
					reportError(state->location, "Expected ' after hex escape");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}

				break;
			}
			case Lexer::CHAR_DEC_ESCAPE: {
				if (c >= '0' && c <= '9') {
					integerValue *= 10;
					integerValue = c - '0';

					if (integerValue > ULANG_MAX) {
						reportError(state->location, "Character value too large");
						return Token(TokenT::INVALID_CHAR, c, ' ');

					}
					continue;
				}
				else if (c == '\'') {
					return Token(TokenT::INT_LITERAL, static_cast<slang>(integerValue));					
				}
				else {
					reportError(state->location, "Expected ' after decimal escape");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}

				break;
			}
			case Lexer::CHAR: {
				if (c == '\\') {
					currentState = Lexer::CHAR_ESCAPE;
				}
				else if (c == EOF) {
					reportError(state->location, "Unexpected end of file in the middle of a character literal");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}
				else if (c < ' ' || c > '~') {
					reportError(state->location, "Chars must only be printable characters, use an escape sequence");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}
				else {
					integerValue = (char) c;
					currentState = Lexer::CHAR_END;
					continue;
				}
				break;
			}
			case Lexer::CHAR_ESCAPE: {
				int escape = getEscapeChar(state, c);

				if (escape >= 0) {
					integerValue = (char) escape;
					currentState = Lexer::CHAR_END;
					continue;
				}
				else {
					reportError(state->location, "Unexpected end of file in the middle of a character escape");
					return Token(TokenT::INVALID_CHAR, c);
				}
				break;
			}
			case Lexer::CHAR_END: {
				if (c == '\'') {
					return Token(TokenT::INT_LITERAL, (slang) integerValue); // Should we preserve the fact that this was a character literal?
				}
				else {
					reportError(state->location, "Expected ' to close character literal, character literals can only contain one character, to have multiple characters use a string");
					return Token(TokenT::INVALID_CHAR, c, ' ');
				}
			}
			case Lexer::HEX: {
				if (c >= '0' && c <= '9') {
					integerValue *= 16;
					integerValue += c - '0';
					continue;
				}
				else if (c >= 'A' && c <= 'F') {
					integerValue *= 16;
					integerValue += c - 'A' + 10;
					continue;
				}
				else if (c >= 'a' && c <= 'f') {
					integerValue *= 16;
					integerValue += c - 'a' + 10;
					continue;
				}
				else if (c == '_') {
					continue;
				}
				else {
					if (c > ULANG_MAX) {
						reportError(state, msg("Integer literal is too large! The maximum value is " << ULANG_MAX));
						return Token(TokenT::INVALID_CHAR, c);
					}

					undoReadChar(state, c);
					return Token(TokenT::INT_LITERAL, static_cast<slang>(integerValue));
				}
				break;
			}
			case Lexer::DEC: {
				if (c >= '0' && c <= '9') {
					integerValue *= 10;
					integerValue += c - '0';
					continue;
				}
				else if (c == '_') {
					continue;
				}
				else {
					if (c > ULANG_MAX) {
						reportError(state, msg("Integer literal is too large! The maximum value is " << ULANG_MAX));
						return Token(TokenT::INVALID_CHAR, c);
					}

					undoReadChar(state, c);
					return Token(TokenT::INT_LITERAL, static_cast<slang>(integerValue));
				}
				break;
			}
			case Lexer::BIN: {
				if (c == '0' || c == '1') {
					integerValue *= 2;
					integerValue += c - '0';
					continue;
				}
				else if (c == '_') {
					continue;
				}
				else {
					if (c > ULANG_MAX) {
						reportError(state, msg("Integer literal is too large! The maximum value is " << ULANG_MAX));
						return Token(TokenT::INVALID_CHAR, c);
					}

					undoReadChar(state, c);
					return Token(TokenT::INT_LITERAL, static_cast<slang>(integerValue));
				}
				break;
			}
			case Lexer::COMMENT: {
				if (c == '\n') {
					currentState = Lexer::DEFAULT;
				}
				else if (c == EOF) {
					return END_OF_FILE;
				}
				continue;
			}
			case Lexer::MULTI_COMMENT: {
				if (c == '*') {
					currentState = Lexer::MULTI_COMMENT_END;
				}
				else if (c == EOF) {
					return END_OF_FILE;
				}
				continue;
			}
			case Lexer::MULTI_COMMENT_END: {
				if (c == '/') {
					currentState = Lexer::DEFAULT;
				}
				else if (c == EOF) {
					return END_OF_FILE;
				}
				else {
					currentState = Lexer::MULTI_COMMENT;
				}
				continue;
			}
			case Lexer::IDENTIFIER: {
				if (isValidIdentifier(c)) {
					state->hasher.append(c);
					continue;
				}
				else {
					PROFILE_ZONE("Lex Identifier");

					undoReadChar(state, c);

					if (state->hasher == TRUE_STRING) {
						return Token(TokenT::INT_LITERAL, 1);
					}
					else if (state->hasher == FALSE_STRING) {
						return Token(TokenT::INT_LITERAL, 0);
					}

					for (const auto &token : keywords) {
						if (state->hasher == token.text) {
							return token;
						}
					}

					AstLeafNode *localVar = resolveInLocalScope(state, state->hasher);

					if (localVar) {
						return Token(localVar);
					}

					return Token(TokenT::IDENTIFIER, String(state->hasher));
				}
				break;
			}
			default:
				assert(false);
		}
	}
}

static Token &next(LexerState *state) {
	state->lastToken = lexerAdvance(state);
	return state->lastToken;
}

static Decl *parseModifiers(LexerState *state, Decl *decl) {
	Token token = next(state);

	if (token == LOCAL) {
		decl->flags |= DECL_IS_LOCAL;
	}
	else if (token == EXTERN) {
		decl->flags |= DECL_IS_EXTERN;
	}
	else {
		return decl;
	}

	token = next(state);

	if (token == LOCAL) {
		if (decl->flags & DECL_IS_LOCAL) {
			reportError(state, "Declaration cannot be marked local multiple times");
			return nullptr;
		}
		else {
			decl->flags |= DECL_IS_LOCAL;
		}
	}
	else if (token == EXTERN) {
		if (decl->flags & DECL_IS_EXTERN) {
			reportError(state, "Declaration cannot be marked extern multiple times");
			return nullptr;
		}
		else {
			decl->flags |= DECL_IS_EXTERN;
		}
	}
	else {
		return decl;
	}

	next(state);

	return decl;
}

static bool isIntegerLiteral(const Token &token) {
	return token.type == TokenT::INT_LITERAL;
}

static bool expectAndConsume(LexerState *state, const Token &token) {
	if (state->lastToken == token) {
		next(state);
		return true;
	}

	return false;
}

static bool isLocalVar(const Token &token) {
	return token.type == TokenT::LOCAL_VAR;
}

static bool isIdentifier(const Token &token) {
	return token.type == TokenT::IDENTIFIER;
}

static bool isStringLiteral(const Token &token) {
	return token.type == TokenT::STRING_LITERAL;
}

static void addToScope(LexerState *state, AstLeafNode *var) {
	state->localScopeStack[state->currentScopeStackDepth - 1].add(var);
}

static void pushScope(LexerState *state) {
	if (state->localScopeStack.size() == state->currentScopeStackDepth) {
		state->localScopeStack.add();
	}

	state->currentScopeStackDepth++;
}

static void popScope(LexerState *state) {
	assert(state->currentScopeStackDepth > 0);
	state->currentScopeStackDepth--;
	state->localScopeStack[state->currentScopeStackDepth].clear();
}

static AstLeafNode *resolveInLocalScope(LexerState *state, const String_Hasher &name) {
	PROFILE_FUNC();
	if (state->currentFunction) {
		for (auto &argument : state->currentFunction->arguments) {
			if (argument->text == name) {
				return argument;
			}
		}

		for (u32 i = 0; i < state->currentScopeStackDepth; i++) {
			for (auto var : state->localScopeStack[i]) {
				if (var->text == name) {
					return var;
				}
			}
		}
	}

	return nullptr;
}

// We assume that any unresolved global that we write to is valid for now, even if it could ba a pointer type global (array or function) which can't be directly written
// @Audit, can we generate a tree that should be assignable but fails this check?
static bool expressionIsAssignable(AstNode *e) {
	switch (e->type) {
		case AstType::LOCAL_VAR:
		case AstType::DEREF:
			return true;
		default:
			reportError(e, "Cannot assign to this expression it is not a local variable, global variable or dereference");
			return false;

	}
}

static AstLeafNode *makeLeafNode(DeclWithExpr *currentDecl, AstType type, const CodeLocation &startLocation, const EndLocation &endLocation) {
	AstLeafNode *node = currentDecl->allocLeafNode();
	node->startLocation = startLocation;
	node->endLocation = endLocation;
	node->type = type;

	return node;
}

static AstLeafNode *makeLocalVar(DeclWithExpr *currentDecl, AstLeafNode *decl, const CodeLocation &startLocation, const EndLocation &endLocation) {
	AstLeafNode *temp = makeLeafNode(currentDecl, AstType::LOCAL_VAR, startLocation, endLocation);
	temp->localIdent = decl;

	return temp;
}

static AstLeafNode *makeLiteral(DeclWithExpr *currentDecl, slang value, const CodeLocation &startLocation, const EndLocation &endLocation) {
	AstLeafNode *leaf = makeLeafNode(currentDecl, AstType::INT_LITERAL, startLocation, endLocation);
	leaf->number = value;

	return leaf;
}

static AstTreeNode *makeTree(DeclWithExpr *currentDecl, AstType type, const CodeLocation &startLocation, const EndLocation &endLocation, SmallArray<AstNode *, 2> nodes) {
	AstTreeNode *tree = currentDecl->allocTreeNode();
	tree->type = type;
	tree->children = nodes;
	tree->startLocation = startLocation;
	tree->endLocation = endLocation;

	return tree;
}

static AstTreeNode *makeDeref(DeclWithExpr *currentDecl, AstLeafNode *decl, const CodeLocation &startLocation, const EndLocation &endLocation) {
	return makeTree(currentDecl, AstType::DEREF, startLocation, endLocation, { makeLocalVar(currentDecl, decl, startLocation, endLocation) });
}

static AstTreeNode *makeLogicNot(DeclWithExpr *currentDecl, AstNode *node, const CodeLocation &startLocation, const EndLocation &endLocation) {
	return makeTree(currentDecl, AstType::EQUAL, startLocation, endLocation,
		{
			node,
			makeLiteral(currentDecl, 0, startLocation, endLocation)
		});
}

static AstTreeNode *makeModifyAssign(DeclWithExpr *currentDecl, AstNode *dest, AstNode *src, AstType type) {
	if (!src) return nullptr;

	if (dest->type == AstType::UNRESOLVED_GLOBAL) {
		// Make sure this assignment gets type checked when the identifier is resolved so that we don't assign to an array or function
		dest->type = AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS;
		dest->flags |= AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN;

		goto deref_removed;
	}

	if (!expressionIsAssignable(dest)) return nullptr;

	if (dest->type == AstType::DEREF) {
		{
			AstTreeNode *tree = static_cast<AstTreeNode *>(dest);
			dest = tree->children[0];
			tree->children.free();
			// delete tree; This shouldn't happen to often so we won't wast much space in the arena
		}

	deref_removed:

		AstLeafNode *varDecl = makeLeafNode(currentDecl, AstType::VAR_DECL, dest->startLocation, dest->endLocation);

		AstTreeNode *assign1 = makeTree(currentDecl, AstType::ASSIGN, dest->startLocation, dest->endLocation,
			{
				makeLocalVar(currentDecl, varDecl, dest->startLocation, dest->endLocation),
				dest
			});

		AstTreeNode *assign2 = makeTree(currentDecl, AstType::ASSIGN, dest->startLocation, src->endLocation,
			{
				makeDeref(currentDecl, varDecl, dest->startLocation, dest->endLocation),
				makeTree(currentDecl, type, dest->startLocation, src->endLocation,
					{
						makeDeref(currentDecl, varDecl, dest->startLocation, dest->endLocation),
						src
					})
			});

		// @Improvement: reuse dest for one of the derefs

		return makeTree(currentDecl, AstType::SEQUENCE, dest->startLocation, src->endLocation,
			{
				varDecl, 
				assign1, 
				assign2
			});
	}
	else {
		// Thanks to expressionIsAssignable we know that if the dest is not a deref it is a leaf since it is some sort of variable, so we don't need a deep copy
		AstLeafNode *destCopy = currentDecl->allocLeafNode();
		*destCopy = *static_cast<AstLeafNode *>(dest);

		return makeTree(currentDecl, AstType::ASSIGN, dest->startLocation, src->endLocation,
			{
			dest,
			makeTree(currentDecl, type, dest->startLocation, src->endLocation,
				{
					destCopy,
					src
				})
			});
	}
}

static AstNode *parseExpression(LexerState *state);

static AstTreeNode *parseModifyAssign(LexerState *state, AstNode *dest, AstType type) {
	AstNode *src = parseExpression(state);

	return makeModifyAssign(state->currentDecl, dest, src, type);
}

static AstTreeNode *makePostModifyAssign(DeclWithExpr *currentDecl, AstNode *dest, const EndLocation &endLocation, AstType type) {
	if (dest->type == AstType::UNRESOLVED_GLOBAL) {
		// Make sure this assignment gets type checked when the identifier is resolved so that we don't assign to an array or function
		dest->type = AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS;
		dest->flags |= AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN;

		goto deref_removed;
	}

	if (!expressionIsAssignable(dest)) return nullptr;

	if (dest->type == AstType::DEREF) {
		{
			AstTreeNode *tree = static_cast<AstTreeNode *>(dest);
			dest = tree->children[0];
			tree->children.free();
			// delete tree; This shouldn't happend to often so we won't wast much space in the arena
		}

	deref_removed:
		const CodeLocation &s = dest->startLocation;
		const EndLocation &e = endLocation;

		AstLeafNode *var1Decl = makeLeafNode(currentDecl, AstType::VAR_DECL, s, e);

		AstLeafNode *var2Decl = currentDecl->allocLeafNode();
		*var2Decl = *var1Decl;


		return makeTree(currentDecl, AstType::SEQUENCE, s, e,
			{
				var1Decl,
				var2Decl,
				makeTree(currentDecl, AstType::ASSIGN, s, e,
					{
						makeLocalVar(currentDecl, var1Decl, s, e),
						dest,
					}),
				makeTree(currentDecl, AstType::ASSIGN, s, e,
					{
						makeLocalVar(currentDecl, var2Decl, s, e),
						makeDeref(currentDecl, var1Decl, s, e),
					}), 
				makeTree(currentDecl, AstType::ASSIGN, s, e,
					{
						makeDeref(currentDecl, var1Decl, s, e),
						makeTree(currentDecl, type, s, e,
							{
								makeLocalVar(currentDecl, var2Decl, s, e),
								makeLiteral(currentDecl, 1, s, e)
							})
					}), 
				makeLocalVar(currentDecl, var2Decl, s, e)
			});
	}
	else {
		const CodeLocation &s = dest->startLocation;
		const EndLocation &e = endLocation;

		AstLeafNode *varDecl = makeLeafNode(currentDecl, AstType::VAR_DECL, s, e);

		return makeTree(currentDecl, AstType::SEQUENCE, s, e,
			{
				varDecl,
				makeTree(currentDecl, AstType::ASSIGN, s, e,
					{
						makeLocalVar(currentDecl, varDecl, s, e),
						dest,
					}),
				makeTree(currentDecl, AstType::ASSIGN, s, e,
					{
						dest,
						makeTree(currentDecl, type, s, e,
							{
								dest,
								makeLiteral(currentDecl, 1, s, e)
							})
					}),
				makeLocalVar(currentDecl, varDecl, s, e)
			});
	}
}

static AstNode *parsePrimaryExpr(LexerState *state) {
	AstNode *e;

	if (state->lastToken.type == TokenT::IDENTIFIER) {
		AstLeafNode *node = makeLeafNode(state->currentDecl, AstType::UNRESOLVED_GLOBAL, state->tokenStartLocation, state->location);
		node->text = state->lastToken.text;
		state->currentDecl->unresolvedIdentifiers.add(node);

		e = node;

		next(state);
	}
	else if (state->lastToken.type == TokenT::LOCAL_VAR) {
		if (state->lastToken.localVar->flags & AST_LOCAL_VAR_IS_DEREF_ITERATOR) {
			e = makeDeref(state->currentDecl, state->lastToken.localVar, state->tokenStartLocation, state->location);
		}
		else {
			e = makeLocalVar(state->currentDecl, state->lastToken.localVar, state->tokenStartLocation, state->location);
		}
		next(state);
	}
	else if (state->lastToken.type == TokenT::INT_LITERAL) {
		e = makeLiteral(state->currentDecl, state->lastToken.value, state->tokenStartLocation, state->location);

		next(state);
	}
	else if (state->lastToken.type == TokenT::STRING_LITERAL) {
		if (!state->currentFunction) {
			reportError(state, "Cannot reference a string literal at compile time");
			return nullptr;
		}

		DeclString *string = new DeclString;
		string->startLocation = state->tokenStartLocation;
		string->endLocation = state->location;
		string->name = state->lastToken.text;

		codeGenQueue.add(string);

		next(state);


		AstLeafNode *node = makeLeafNode(state->currentDecl, AstType::GLOBAL_POINTER, string->startLocation, string->endLocation);
		node->globalIdent = string;
		
		e = node;

	}
	else if (state->lastToken == OPEN_PAREN) {
		next(state);

		e = parseExpression(state);

		if (!e) return nullptr;

		if (!expectAndConsume(state, CLOSE_PAREN)) {
			reportError(state, "Expected ) after expression");
			return nullptr;
		}
	}
	else if (state->lastToken == OPEN_SQUARE) { // Open square for local array creation, not indexing
		if (!state->currentFunction) {
			reportError(state, "Cannot allocate an array at compile time");
			return nullptr;
		}

		CodeLocation start = state->tokenStartLocation;

		next(state);

		EndLocation close = state->location;

		e = parseExpression(state);

		if (!e) return nullptr;

		close = state->location;

		if (!expectAndConsume(state, CLOSE_SQUARE)) {
			reportError(state, expected("Expected ] after expression in array allocator", state->lastToken));
			return nullptr;
		}

		AstTreeNode *array = makeTree(state->currentDecl, AstType::ARRAY, start, close, { e });

		if (expectAndConsume(state, OPEN_CURLY)) {

			AstLeafNode *varDecl = makeLeafNode(state->currentDecl, AstType::VAR_DECL, start, close);

			AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, start, close,
				{
					varDecl,
					makeTree(state->currentDecl, AstType::ASSIGN, start, close,
						{
							makeLocalVar(state->currentDecl, varDecl, start, close),
							array
						})
				});

			ulang count = 0;

			sequence->endLocation = state->location;

			while (!expectAndConsume(state, CLOSE_CURLY)) {
				AstNode *init = parseExpression(state);
				sequence->children.add(makeTree(state->currentDecl, AstType::ASSIGN, init->startLocation, init->endLocation,
					{
						makeTree(state->currentDecl, AstType::DEREF, init->startLocation, init->endLocation,
							{
								makeTree(state->currentDecl, AstType::ADD, init->startLocation, init->endLocation,
									{
										makeLocalVar(state->currentDecl, varDecl, init->startLocation, init->endLocation),
										makeLiteral(state->currentDecl, static_cast<slang>(count), init->startLocation, init->endLocation)
									}),
							}),
						init
					}));

				++count;

				if (!expectAndConsume(state, COMMA)) { // If we get a comma, continue and do the close curly check at the top of the loop to allow trailing comma, otherwise if no comma there must be a close curly following and we break

					sequence->endLocation = state->location;
					if (expectAndConsume(state, CLOSE_CURLY)) {
						break;
					}
					else {
						reportError(state, expected("Expected , or } in array initializer", state->lastToken));
						return nullptr;
					}
				}
			}

			if (count == 0) {
				reportWarning(WARNING_ZERO_SIZE_ARRAY_INITIALIZER, sequence, "Zero-length initializer used in array allocation, no values in array will actually be initialized, values will not default to 0.");
			}
			else if (e->type == AstType::INT_LITERAL) {
				AstLeafNode *leaf = static_cast<AstLeafNode *>(e);

				if (count < leaf->unumber) {
					reportWarning(WARNING_INITIALIZER_WRONG_SIZE, sequence, msg("Array initializer length of " << count << " is smaller than allocation size of " << leaf->unumber << " the remaining values in the array will not be initialized"));
				}
				else if (count > leaf->unumber) {
					reportWarning(WARNING_INITIALIZER_WRONG_SIZE, sequence, msg("Array initializer length of " << count << " is larger than allocation size of " << leaf->unumber << " the initializer will write out of bounds of the array"));
				}
			}


			if (state->forIncrementStack.size()) {
				reportWarning(WARNING_ARRAY_ALLOCATION_IN_LOOP, sequence, "Stack allocation of array in loop will allocate multiple separate arrays");
			}

			sequence->children.add(makeLocalVar(state->currentDecl, varDecl, sequence->startLocation, sequence->endLocation));


			e = sequence;
		}
		else {
			if (state->forIncrementStack.size()) {
				reportWarning(WARNING_ARRAY_ALLOCATION_IN_LOOP, array, "Stack allocation of array in loop will allocate multiple separate arrays");
			}

			e = array;
		}
	}
	else if (state->lastToken == OPEN_CURLY) {
		if (!state->currentFunction) {
			reportError(state, "Cannot allocate an array at compile time");
			return nullptr;
		}

		AstLeafNode *varDecl = makeLeafNode(state->currentDecl, AstType::VAR_DECL, state->tokenStartLocation, state->location);

		AstTreeNode *array = makeTree(state->currentDecl, AstType::ARRAY, varDecl->startLocation, varDecl->endLocation, {});

		AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, varDecl->startLocation, varDecl->endLocation,
			{
				varDecl,
				makeTree(state->currentDecl, AstType::ASSIGN, varDecl->startLocation, varDecl->endLocation,
					{
						makeLocalVar(state->currentDecl, varDecl, varDecl->startLocation, varDecl->endLocation),
						array
					})
			});

		ulang count = 0;

		sequence->endLocation = state->location;

		next(state);

		while (!expectAndConsume(state, CLOSE_CURLY)) {
			AstNode *init = parseExpression(state);
			sequence->children.add(makeTree(state->currentDecl, AstType::ASSIGN, init->startLocation, init->endLocation,
				{
					makeTree(state->currentDecl, AstType::DEREF, init->startLocation, init->endLocation,
						{
							makeTree(state->currentDecl, AstType::ADD, init->startLocation, init->endLocation,
								{
									makeLocalVar(state->currentDecl, varDecl, init->startLocation, init->endLocation),
									makeLiteral(state->currentDecl, static_cast<slang>(count), init->startLocation, init->endLocation)
								}),
						}),
					init
				}));

			++count;

			if (!expectAndConsume(state, COMMA)) { // If we get a comma, continue and do the close curly check at the top of the loop to allow trailing comma, otherwise if no comma there must be a close curly following and we break

				sequence->endLocation = state->location;
				if (expectAndConsume(state, CLOSE_CURLY)) {
					break;
				}
				else {
					reportError(state, expected("Expected , or } in array initializer", state->lastToken));
					return nullptr;
				}
			}
		}

		array->children.add(makeLiteral(state->currentDecl, static_cast<ulang>(count), array->startLocation, array->endLocation));
		sequence->children.add(makeLocalVar(state->currentDecl, varDecl, sequence->startLocation, sequence->endLocation));


		if (count == 0) {
			reportWarning(WARNING_ZERO_SIZE_ARRAY, sequence, "Allocation of zero size array has no purpose");
		}

		if (state->forIncrementStack.size()) {
			reportWarning(WARNING_ARRAY_ALLOCATION_IN_LOOP, sequence, "Stack allocation of array in loop will allocate multiple separate arrays");
		}

		e = sequence;

	}
	else {
		reportError(state, expected("Expected term in expression", state->lastToken));
		return nullptr;
	}

	while (true) {
		EndLocation location = state->location;

		if (expectAndConsume(state, INCREMENT)) {
			if (!state->currentFunction) {
				reportError(state, "Cannot modify a variable at compile time");
				return nullptr;
			}
			e = makePostModifyAssign(state->currentDecl, e, location, AstType::ADD);

			if (!e) return nullptr;
		}
		else if (expectAndConsume(state, DECREMENT)) {
			if (!state->currentFunction) {
				reportError(state, "Cannot modify a variable at compile time");
				return nullptr;
			}
			e = makePostModifyAssign(state->currentDecl, e, location, AstType::SUB);

			if (!e) return nullptr;
		}
		else if (expectAndConsume(state, OPEN_PAREN)) {
			if (!state->currentFunction) {
				reportError(state, "Cannot call a function");
				return nullptr;
			}
			AstTreeNode *call = makeTree(state->currentDecl, AstType::CALL, e->startLocation, location, { e });

			while (!expectAndConsume(state, CLOSE_PAREN)) {
				AstNode *argument = parseExpression(state);

				if (!argument) return nullptr;

				call->children.add(argument);

				if (!expectAndConsume(state, COMMA)) { // If we get a comma, continue and do the close curly check at the top of the loop to allow trailing comma, otherwise if no comma there must be a close curly following and we break

					call ->endLocation = state->location;
					if (expectAndConsume(state, CLOSE_PAREN)) {
						break;
					}
					else {
						reportError(state, expected("Expected , or ) in function call arguments", state->lastToken));
						return nullptr;
					}
				}
			}

			e = call;
		}
		else if (expectAndConsume(state, OPEN_SQUARE)) {
			if (!state->currentFunction) {
				reportError(state, "Cannot dereference at compile time");
				return nullptr;
			}

			AstNode *index = parseExpression(state);

			location = state->location;
			if (!expectAndConsume(state, CLOSE_SQUARE)) { 
				reportError(state, expected("Expected ] in array index", state->lastToken));
				return nullptr; 
			}

			e = makeTree(state->currentDecl, AstType::DEREF, e->startLocation, location,
				{
					makeTree(state->currentDecl, AstType::ADD, e->startLocation, location, 
						{
							e, 
							index
						})
				});
		}
		else {
			break;
		}
	}

	return e;
}

static AstNode *parseUnaryExpr(LexerState *state);

static AstNode *parseLogicNot(const CodeLocation &begin, LexerState *state) {
	AstNode *e = parseUnaryExpr(state);

	if (!e) return nullptr;

	return makeLogicNot(state->currentDecl, e, begin, e->endLocation);
}

static AstNode *parseUnaryExpr(LexerState *state) {
	CodeLocation begin = state->tokenStartLocation;

	if (expectAndConsume(state, ASTERISK)) {
		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		if (e->type == AstType::ADROF) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);

			AstNode *inner = tree->children[0];

			tree->children.free();
			// delete tree; This shouldn't happend to often so we won't wast much space in the arena

			return inner;
		}
		else {
			if (!state->currentFunction) {
				reportError(state, "Cannot dereference at compile time");
				return nullptr;
			}

			return makeTree(state->currentDecl, AstType::DEREF, begin, e->endLocation, { e });
		}
	}
	else if (expectAndConsume(state, BIT_AND)) {
		if (!state->currentFunction) {
			reportError(state, "Cannot take an address at compile time");
			return nullptr;
		}

		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		if (e->type == AstType::DEREF) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);

			AstNode *inner = tree->children[0];

			tree->children.free();
			// delete tree; This shouldn't happend to often so we won't wast much space in the arena

			return inner;
		}
		else {
			if (e->type == AstType::UNRESOLVED_GLOBAL) {
				e->type = AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS; // To take the address of something it must be a global varaiable

				return e;
			}
			else {
				reportError(e, "Cannot take the address of something that is not a dereference or global variable");
				return nullptr;
			}
		}
	}
	else if (expectAndConsume(state, MINUS)) {
		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		if (e->type == AstType::NEG) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);

			AstNode *inner = tree->children[0];

			tree->children.free();
			// delete tree; // This shouldn't happend to often so we won't wast much space in the arena @Leak

			return inner;
		}
		else {
			return makeTree(state->currentDecl, AstType::NEG, begin, e->endLocation, { e });
		}
	}
	else if (expectAndConsume(state, PLUS)) {
		return parseUnaryExpr(state);
	}
	else if (expectAndConsume(state, INCREMENT)) {
		if (!state->currentFunction) {
			reportError(state, "Cannot modify a variable at compile time");
			return nullptr;
		}

		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		return makeModifyAssign(state->currentDecl, e, makeLiteral(state->currentDecl, 1, begin, e->endLocation), AstType::ADD);
	}
	else if (expectAndConsume(state, DECREMENT)) {
		if (!state->currentFunction) {
			reportError(state, "Cannot modify a variable at compile time");
			return nullptr;
		}

		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		return makeModifyAssign(state->currentDecl, e, makeLiteral(state->currentDecl, 1, begin, e->endLocation), AstType::SUB);
	}
	else if (expectAndConsume(state, BIT_NOT)) {
		AstNode *e = parseUnaryExpr(state);

		if (!e) return nullptr;

		if (e->type == AstType::BIT_NOT) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);

			AstNode *inner = tree->children[0];

			tree->children.free();
			// delete tree; This shouldn't happend to often so we won't wast much space in the arena

			return inner;
		}
		else {
			return makeTree(state->currentDecl, AstType::BIT_NOT, begin, e->endLocation, { e });
		}
	}
	else if (expectAndConsume(state, LOGIC_NOT)) {
		return parseLogicNot(begin, state);
	}

	AstNode *expr = parsePrimaryExpr(state);

	return expr;
}

static AstNode *parseMulExpr(LexerState *state) {
	AstNode *e = parseUnaryExpr(state);

	if (!e) return nullptr;

	while (true) {
		if (expectAndConsume(state, ASTERISK)) {
			AstNode *e2 = parseUnaryExpr(state);

			if (!e2) return nullptr;

			if (e->type == AstType::MUL) {
				AstTreeNode *tree = static_cast<AstTreeNode *>(e);
				tree->children.add(e2);
				tree->endLocation = e2->endLocation;
			}
			else {
				e = makeTree(state->currentDecl, AstType::MUL, e->startLocation, e2->endLocation,
					{
						e,
						e2
					});
			}
		}
		else if (expectAndConsume(state, SLASH)) {
			AstNode *e2 = parseUnaryExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::DIV, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, MODULO)) {
			AstNode *e2 = parseUnaryExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::MOD, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else {
			break;
		}
	}

	return e;
}

static AstNode *parseAddExpr(LexerState *state) {
	AstNode *e = parseMulExpr(state);

	if (!e) return nullptr;

	while (true) {
		if (expectAndConsume(state, PLUS)) {
			AstNode *e2 = parseMulExpr(state);

			if (!e2) return nullptr;

			if (e->type == AstType::ADD) {
				AstTreeNode *tree = static_cast<AstTreeNode *>(e);
				tree->children.add(e2);
				tree->endLocation = e2->endLocation;
			}
			else {
				e = makeTree(state->currentDecl, AstType::ADD, e->startLocation, e2->endLocation,
					{
						e,
						e2
					});
			}
		}
		else if (expectAndConsume(state, MINUS)) {
			AstNode *e2 = parseMulExpr(state);

			if (!e2) return nullptr;

			if (e->type == AstType::SUB) {
				AstTreeNode *tree = static_cast<AstTreeNode *>(e);
				tree->children.add(e2);
				tree->endLocation = e2->endLocation;
			}
			else {
				e = makeTree(state->currentDecl, AstType::SUB, e->startLocation, e2->endLocation,
					{
						e,
						e2
					});
			}
		}
		else {
			break;
		}
	}

	return e;
}

static AstNode *parseShiftExpr(LexerState *state) {
	AstNode *e = parseAddExpr(state);

	if (!e) return nullptr;

	while (true) {
		if (expectAndConsume(state, LSHIFT) || expectAndConsume(state, ALSHIFT)) {
			AstNode *e2 = parseAddExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::LSHIFT, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, RSHIFT)) {
			AstNode *e2 = parseAddExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::URSHIFT, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, ARSHIFT)) {
			AstNode *e2 = parseAddExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::RSHIFT, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else {
			break;
		}
	}

	return e;
}

static AstNode *parseCompExpr(LexerState *state) {
	AstNode *e = parseShiftExpr(state);

	if (!e) return nullptr;

	while (true) {
		if (expectAndConsume(state, LESS)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::LESS, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, GREATER)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::GREATER, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, U_LESS)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::ULESS, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, U_GREATER)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::UGREATER, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, GREATER_OR_EQUAL)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeLogicNot(state->currentDecl, makeTree(state->currentDecl, AstType::LESS, e->startLocation, e2->endLocation,
				{
					e,
					e2
				}), e->startLocation, e2->endLocation);
		}
		else if (expectAndConsume(state, LESS_OR_EQUAL)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeLogicNot(state->currentDecl, makeTree(state->currentDecl, AstType::GREATER, e->startLocation, e2->endLocation,
				{
					e,
					e2
				}), e->startLocation, e2->endLocation);
		}
		else if (expectAndConsume(state, U_GREATER_OR_EQUAL)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeLogicNot(state->currentDecl, makeTree(state->currentDecl, AstType::ULESS, e->startLocation, e2->endLocation,
				{
					e,
					e2
				}), e->startLocation, e2->endLocation);
		}
		else if (expectAndConsume(state, U_LESS_OR_EQUAL)) {
			AstNode *e2 = parseShiftExpr(state);

			if (!e2) return nullptr;

			e = makeLogicNot(state->currentDecl, makeTree(state->currentDecl, AstType::UGREATER, e->startLocation, e2->endLocation,
				{
					e,
					e2
				}), e->startLocation, e2->endLocation);
		}
		else {
			break;
		}
	}

	return e;
}

static AstNode *parseEqExpr(LexerState *state) {
	AstNode *e = parseCompExpr(state);

	if (!e) return nullptr;

	while (true) {
		if (expectAndConsume(state, EQUALITY)) {
			AstNode *e2 = parseCompExpr(state);

			if (!e2) return nullptr;

			e = makeTree(state->currentDecl, AstType::EQUAL, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
		else if (expectAndConsume(state, NOT_EQUAL)) {
			AstNode *e2 = parseCompExpr(state);

			if (!e2) return nullptr;

			e = makeLogicNot(state->currentDecl, makeTree(state->currentDecl, AstType::EQUAL, e->startLocation, e2->endLocation,
						{
							e,
							e2
						}), e->startLocation, e2->endLocation);
		}
		else {
			break;
		}
	}

	return e;
}


static AstNode *parseBandExpr(LexerState *state) {
	AstNode *e = parseEqExpr(state);

	if (!e) return nullptr;

	while (expectAndConsume(state, BIT_AND)) {
		AstNode *e2 = parseEqExpr(state);

		if (!e2) return nullptr;

		if (e->type == AstType::BIT_AND) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);
			tree->children.add(e2);
			tree->endLocation = e2->endLocation;
		}
		else {
			e = makeTree(state->currentDecl, AstType::BIT_AND, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
	}

	return e;
}

static AstNode *parseXorExpr(LexerState *state) {
	AstNode *e = parseBandExpr(state);

	if (!e) return nullptr;

	while (expectAndConsume(state, BIT_XOR)) {
		AstNode *e2 = parseBandExpr(state);

		if (!e2) return nullptr;

		if (e->type == AstType::XOR) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);
			tree->children.add(e2);
			tree->endLocation = e2->endLocation;
		}
		else {
			e = makeTree(state->currentDecl, AstType::XOR, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
	}

	return e;
}

static AstNode *parseBorExpr(LexerState *state) {
	AstNode *e = parseXorExpr(state);

	if (!e) return nullptr;

	while (expectAndConsume(state, BIT_OR)) {
		AstNode *e2 = parseXorExpr(state);

		if (!e2) return nullptr;

		if (e->type == AstType::BIT_OR) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);
			tree->children.add(e2);
			tree->endLocation = e2->endLocation;
		}
		else {
			e = makeTree(state->currentDecl, AstType::BIT_OR, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
	}

	return e;
}

static AstNode *parseLandExpr(LexerState *state) {
	AstNode *e = parseBorExpr(state);

	if (!e) return nullptr;

	while (expectAndConsume(state, LOGIC_AND)) {
		AstNode *e2 = parseBorExpr(state);

		if (!e2) return nullptr;

		if (e->type == AstType::L_AND) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);
			tree->children.add(e2);
			tree->endLocation = e2->endLocation;
		}
		else {
			e = makeTree(state->currentDecl, AstType::L_AND, e->startLocation, e2->endLocation,
				{
					e,
					e2
				});
		}
	}

	return e;
}

static AstNode *parseLorExpr(LexerState *state) {
	AstNode *e = parseLandExpr(state);

	if (!e) return nullptr;

	while (expectAndConsume(state, LOGIC_OR)) {
		AstNode *e2 = parseLandExpr(state);

		if (!e2) return nullptr;

		if (e->type == AstType::L_OR) {
			AstTreeNode *tree = static_cast<AstTreeNode *>(e);
			tree->children.add(e2);
			tree->endLocation = e2->endLocation;
		}
		else {
			e = makeTree(state->currentDecl, AstType::L_OR, e->startLocation, e2->endLocation,
				{
					e, 
					e2
				});
		}
	}

	return e;
}

static AstNode *parseTernaryExpr(LexerState *state) {
	AstNode *condition = parseLorExpr(state);

	if (!condition) return nullptr;

	if (expectAndConsume(state, QUESTION)) {
		AstNode *true_ = parseExpression(state);

		if (!true_) return nullptr;

		if (!expectAndConsume(state, COLON)) return nullptr;

		AstNode *false_ = parseTernaryExpr(state);

		if (!false_) return nullptr;

		return makeTree(state->currentDecl, AstType::TERNARY, condition->startLocation, false_->endLocation,
			{
				condition,
				true_,
				false_
			});
	}

	return condition;
}

static AstNode *parseExpression(LexerState *state) {
	PROFILE_FUNC();
	AstNode *dest = parseTernaryExpr(state);

	if (!dest) return nullptr;

	if (expectAndConsume(state, ASSIGN)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		if (dest->type == AstType::UNRESOLVED_GLOBAL) {
			// Make sure this assignment gets type checked when the identifier is resolved so that we don't assign to an array or function
			dest->type = AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS;
			dest->flags |= AST_GLOBAL_VAR_ADDRESS_IS_FROM_ASSIGN;

			dest = makeTree(state->currentDecl, AstType::DEREF, dest->startLocation, dest->endLocation, { dest });
		}

		if (!expressionIsAssignable(dest)) return nullptr;
		
		AstNode *src = parseExpression(state);

		if (!src) return nullptr;


		AstTreeNode *node = makeTree(state->currentDecl, AstType::ASSIGN, dest->startLocation, dest->endLocation, 
			{
				dest, 
				src
			});

		return node;
	}
	else if (expectAndConsume(state, PLUS_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::ADD);
	}
	else if (expectAndConsume(state, MINUS_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::SUB);
	}
	else if (expectAndConsume(state, TIMES_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::MUL);
	}
	else if (expectAndConsume(state, DIVIDE_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::DIV);
	}
	else if (expectAndConsume(state, MODULO_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::MOD);
	}
	else if (expectAndConsume(state, ALSHIFT_EQUALS) || expectAndConsume(state, LSHIFT_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::LSHIFT);
	}
	else if (expectAndConsume(state, ARSHIFT_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::RSHIFT);
	}
	else if (expectAndConsume(state, RSHIFT_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::URSHIFT);
	}
	else if (expectAndConsume(state, BIT_AND_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::BIT_AND);
	}
	else if (expectAndConsume(state, BIT_OR_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::BIT_OR);
	}
	else if (expectAndConsume(state, XOR_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::XOR);
	}
	else if (expectAndConsume(state, LOGIC_AND_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::L_AND);
	}
	else if (expectAndConsume(state, LOGIC_OR_EQUALS)) {
		if (!state->currentFunction) {
			reportError("Cannot make assignments in compile time expressions");
			return nullptr;
		}

		return parseModifyAssign(state, dest, AstType::L_OR);
	}

	return dest;
}

static AstNode *parseStatement(LexerState *state);

static AstNode *parseCompoundStatement(LexerState *state) {
	PROFILE_FUNC();
	AstTreeNode *sequence = state->currentDecl->allocTreeNode();
	sequence->type = AstType::SEQUENCE;

	sequence->startLocation = state->tokenStartLocation;

	next(state);

	pushScope(state);
	while (state->lastToken != CLOSE_CURLY) {
		AstNode *stmt = parseStatement(state);

		if (!stmt) return nullptr;

		sequence->children.add(stmt);
	}
	popScope(state);

	sequence->endLocation = state->location;

	next(state);

	return sequence;
}

static AstNode *parseVarStatement(LexerState *state) {
	AstLeafNode *varDecl = state->currentDecl->allocLeafNode();
	varDecl->type = AstType::VAR_DECL;
	varDecl->startLocation = state->tokenStartLocation;

	next(state);

	if (isLocalVar(state->lastToken)) {
		reportError(state, msg("Variable " << state->lastToken.localVar->text << " is already defined at " << state->lastToken.localVar->startLocation << " local variables cannot be redeclared"));
		return nullptr;
	}

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected name of variable", state->lastToken));
		return nullptr;
	}

	varDecl->text = state->lastToken.text;
	
	varDecl->endLocation = state->location;

	next(state);

	if (state->lastToken == SEMICOLON) {
		addToScope(state, varDecl);
		next(state);

		return varDecl;
	}
	else if (expectAndConsume(state, ASSIGN)) {
		AstNode *expr = parseExpression(state);

		// @Improvement: Maybe add a better error message if the variable is used in its own declaration, currently it will end up as an unresolved global
		addToScope(state, varDecl); // Add the variable after we parse it's initialization so its initialization doesn't self-reference

		if (!expr) return nullptr;
		

		AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, varDecl->startLocation, state->location,
			{
				varDecl,
				makeTree(state->currentDecl, AstType::ASSIGN, varDecl->startLocation, state->location,
					{
						makeLocalVar(state->currentDecl, varDecl, varDecl->startLocation, varDecl->endLocation), 
						expr
					})
			});

		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after variable declaration", state->lastToken));
			return nullptr;
		}

		return sequence;
	}
	else {
		reportError(state, expected("Expected = or ; after variable declaration", state->lastToken));
		return nullptr;
	}
}

static AstNode *parseForStatement(LexerState *state) {
	AstTreeNode *loop = state->currentDecl->allocTreeNode();
	loop->type = AstType::LOOP;
	loop->startLocation = state->tokenStartLocation;


	next(state);

	if (!expectAndConsume(state, OPEN_PAREN)) {
		reportError(state, expected("Expected ( at the start of for loop", state->lastToken));
		return nullptr;
	}

	AstTreeNode *node = loop;

	pushScope(state);
	if (state->lastToken == VAR) {

		AstNode *varDecl = parseVarStatement(state);

		if (!varDecl) return nullptr;
	
		node = state->currentDecl->allocTreeNode();
		node->type = AstType::SEQUENCE;
		node->startLocation = loop->startLocation;
		node->children.add(varDecl);
		node->children.add(loop);
	}
	else if (!expectAndConsume(state, SEMICOLON)) {
		AstNode *expr = parseExpression(state);

		if (!expr) return nullptr;

		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after for loop initializer expression", state->lastToken));
			return nullptr;
		}

		node = state->currentDecl->allocTreeNode();
		node->type = AstType::SEQUENCE;
		node->startLocation = loop->startLocation;
		node->children.add(expr);
		node->children.add(loop);
	}

	CodeLocation start = state->tokenStartLocation;

	if (expectAndConsume(state, SEMICOLON)) {
		AstLeafNode *true_ = makeLiteral(state->currentDecl, 1, start, start);

		loop->children.add(true_);
	}
	else {
		AstNode *expr = parseExpression(state);

		if (!expr) return nullptr;

		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after for loop condition", state->lastToken));
			return nullptr;
		}

		loop->children.add(expr);
	}

	if (expectAndConsume(state, CLOSE_PAREN)) {
		state->forIncrementStack.add(nullptr);
	}
	else {
		AstNode *expr = parseExpression(state);

		if (!expr) return nullptr;

		if (!expectAndConsume(state, CLOSE_PAREN)) {
			reportError(state, expected("Expected ) after for loop increment", state->lastToken));
			return nullptr;
		}

		state->forIncrementStack.add(expr);
	}

	AstNode *body = parseStatement(state);

	if (!body) return nullptr;

	assert(state->forIncrementStack.size());

	if (state->forIncrementStack[state->forIncrementStack.size() - 1]) {
		AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, body->startLocation, body->endLocation,
			{
				body,
				state->forIncrementStack[state->forIncrementStack.size() - 1]
			});

		body = sequence;
	}

	
	loop->children.add(body);
	loop->endLocation = state->tokenStartLocation;
	node->endLocation = state->tokenStartLocation;

	popScope(state);
	state->forIncrementStack.pop();

	return node;
}

static AstNode *parseEachStatement(LexerState *state) {
	AstTreeNode *sequence = state->currentDecl->allocTreeNode();
	sequence->type = AstType::SEQUENCE;

	AstTreeNode *loop = state->currentDecl->allocTreeNode();
	loop->type = AstType::LOOP;
	loop->startLocation = state->tokenStartLocation;


	next(state);

	if (!expectAndConsume(state, OPEN_PAREN)) {
		reportError(state, expected("Expected ( at the start of for loop", state->lastToken));
		return nullptr;
	}

	pushScope(state);
	
	bool deref = expectAndConsume(state, ASTERISK);

	if (isLocalVar(state->lastToken)) {
		reportError(state, msg("Variable " << state->lastToken.localVar->text << " is already defined at " << state->lastToken.localVar->startLocation << " local variables cannot be redeclared"));
		return nullptr;
	}

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected name of variable", state->lastToken));
		return nullptr;
	}

	AstLeafNode *iterator = state->currentDecl->allocLeafNode();
	iterator->startLocation = state->tokenStartLocation;
	iterator->endLocation = state->location;
	iterator->type = AstType::VAR_DECL;
	iterator->text = state->lastToken.text;

	sequence->children.add(iterator);

	if (deref) {
		iterator->flags |= AST_LOCAL_VAR_IS_DEREF_ITERATOR;
	}

	addToScope(state, iterator);

	next(state);


	AstLeafNode *iteratorIndex = nullptr;
	if (expectAndConsume(state, COMMA)) {
		if (isLocalVar(state->lastToken)) {
			reportError(state, msg("Variable " << state->lastToken.localVar->text << " is already defined at " << state->lastToken.localVar->startLocation << " local variables cannot be redeclared"));
			return nullptr;
		}

		if (!isIdentifier(state->lastToken)) {
			reportError(state, expected("Expected name of variable", state->lastToken));
			return nullptr;
		}

		iteratorIndex = state->currentDecl->allocLeafNode();
		iteratorIndex->startLocation = state->tokenStartLocation;
		iteratorIndex->endLocation = state->location;
		iteratorIndex->type = AstType::VAR_DECL;
		iteratorIndex->text = state->lastToken.text;

		sequence->children.add(iteratorIndex);

		addToScope(state, iteratorIndex);

		next(state);
	}

	if (!expectAndConsume(state, COLON)) {
		reportError(state, expected("Expected : after each loop iterators", state->lastToken));
		return nullptr;
	}

	AstNode *init = parseExpression(state);
	if (!init) return nullptr;

	bool range;
	AstNode *bound;

	if (expectAndConsume(state, COMMA)) {
		range = false;
	}
	else if (expectAndConsume(state, RANGE)) {
		range = true;
	}
	else if (expectAndConsume(state, CLOSE_PAREN)) {
		range = false;
		loop->endLocation = state->location;
		sequence->endLocation = state->location;

		bound = init;
		init = makeLiteral(state->currentDecl, 0, loop->startLocation, loop->endLocation);
		goto skipClose;
	}
	else {
		reportError(state, expected("Expected , or .. after initial value in each loop", state->lastToken));
		return nullptr;
	}

	bound = parseExpression(state);
	
	loop->endLocation = state->location;
	sequence->endLocation = state->location;

	if (!expectAndConsume(state, CLOSE_PAREN)) {
		reportError(state, expected("Expected ) after each loop bound", state->lastToken));
	}

	skipClose:

	auto &c = state->currentDecl;
	auto &s = loop->startLocation;
	auto &e = bound->endLocation;


	AstLeafNode *initVar = nullptr;

	AstLeafNode *boundVar = makeLeafNode(c, AstType::VAR_DECL, s, e);

	sequence->children.add(boundVar);
	
	if (range || !iteratorIndex) {
		sequence->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, iterator, s, e),
				init
			}));
	}
	else {
		initVar = makeLeafNode(c, AstType::VAR_DECL, s, e);

		sequence->children.add(initVar);

		sequence->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, initVar, s, e),
				init
			}));
	}

	if (iteratorIndex) {
		sequence->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, iteratorIndex, s, e),
				makeLiteral(c, 0, s, e)
			}));
	}

	if (range || iteratorIndex) {
		sequence->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, boundVar, s, e),
				bound
			}));
	}
	else {
		sequence->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, boundVar, s, e),
				makeTree(c, AstType::ADD, s, e,
					{
						makeLocalVar(c, iterator, s, e), 
						bound
					})
			}));
	}

	sequence->children.add(loop);

	AstTreeNode *increment;
	if (!range && iteratorIndex) {
		increment = makeModifyAssign(c, makeLocalVar(c, iteratorIndex, s, e), makeLiteral(c, 1, s, e), AstType::ADD);
	}
	else if (iteratorIndex) {
		increment = makeTree(c, AstType::SEQUENCE, s, e,
			{
				makeModifyAssign(c, makeLocalVar(c, iterator, s, e), makeLiteral(c, 1, s, e), AstType::ADD),
				makeModifyAssign(c, makeLocalVar(c, iteratorIndex, s, e), makeLiteral(c, 1, s, e), AstType::ADD)
			});
	}
	else {
		increment = makeModifyAssign(c, makeLocalVar(c, iterator, s, e), makeLiteral(c, 1, s, e), AstType::ADD);
	}

	if (range || !iteratorIndex) {
		loop->children.add(makeLogicNot(c, makeTree(c, AstType::EQUAL, s, e,
			{
				makeLocalVar(c, iterator, s,  e),
				makeLocalVar(c, boundVar, s, e)
			}), s, e));
	}
	else {
		loop->children.add(makeLogicNot(c, makeTree(c, AstType::EQUAL, s, e,
			{
				makeLocalVar(c, iteratorIndex, s,  e),
				makeLocalVar(c, boundVar, s, e)
			}), s, e));
	}
	
	state->forIncrementStack.add(increment);

	AstNode *body = parseStatement(state);

	if (!body) return nullptr;

	AstTreeNode *node = state->currentDecl->allocTreeNode();
	node->startLocation = s;
	node->endLocation = e;
	node->type = AstType::SEQUENCE;
	
	if (!range && iteratorIndex) {
		node->children.add(makeTree(c, AstType::ASSIGN, s, e,
			{
				makeLocalVar(c, iterator, s, e),
				makeTree(c, AstType::ADD, s, e, 
					{
						makeLocalVar(c, initVar, s, e),
						makeLocalVar(c, iteratorIndex, s, e)
					})
			}));
	}

	node->children.add(body);
	node->children.add(increment);

	loop->children.add(node);

	assert(state->forIncrementStack.size());
	popScope(state);
	state->forIncrementStack.pop();

	return sequence;
}

static AstNode *parseWhileStatement(LexerState *state) {
	AstTreeNode *loop = state->currentDecl->allocTreeNode();
	loop->type = AstType::LOOP;
	loop->startLocation = state->tokenStartLocation;


	next(state);

	if (!expectAndConsume(state, OPEN_PAREN)) {
		reportError(state, expected("Expected ( at the start of while loop", state->lastToken));
		return nullptr;
	};

	AstNode *expr = parseExpression(state);

	if (!expr) return nullptr;

	if (!expectAndConsume(state, CLOSE_PAREN)) {
		reportError(state, expected("Expected ) after while loop condition", state->lastToken));
		return nullptr;
	}

	loop->children.add(expr);


	state->forIncrementStack.add(nullptr);
	pushScope(state);

	AstNode *body = parseStatement(state);

	if (!body) return nullptr;


	loop->children.add(body);
	loop->endLocation = state->tokenStartLocation;

	popScope(state);
	state->forIncrementStack.pop();

	return loop;
}

static AstNode *parseIfStatement(LexerState *state) {
	CodeLocation ifStart = state->tokenStartLocation;

	next(state);

	if (!expectAndConsume(state, OPEN_PAREN)) {
		reportError(state, expected("Expected ( at the start of if statement", state->lastToken));
		return nullptr;
	}

	AstNode *condition = parseExpression(state);

	if (!condition) return nullptr;

	if (!expectAndConsume(state, CLOSE_PAREN)) {
		reportError(state, expected("Expected ) after if statement condition", state->lastToken));
		return nullptr;
	}

	pushScope(state);
	AstNode *ifBody = parseStatement(state);
	popScope(state);
	AstNode *elseBody = nullptr;

	if (!ifBody) return nullptr;

	if (expectAndConsume(state, ELSE)) {
		pushScope(state);
		elseBody = parseStatement(state);
		popScope(state);

		if (!elseBody) return nullptr;
	}

	if (elseBody) {
		return makeTree(state->currentDecl, AstType::IF_ELSE, ifStart, elseBody->endLocation,
			{
				condition, 
				ifBody, 
				elseBody
			});
	}
	else {
		return makeTree(state->currentDecl, AstType::IF_ELSE, ifStart, ifBody->endLocation,
			{
				condition,
				ifBody
			});
	}
}


static AstNode *parseStatement(LexerState *state) {
	if (state->lastToken == OPEN_CURLY) {
		return parseCompoundStatement(state);
	}
	else if (state->lastToken == BREAK) {
		if (state->forIncrementStack.size() == 0) {
			reportError(state, "Cannot have a break statement outside of a loop");
			return nullptr;
		}

		AstLeafNode *expr = makeLeafNode(state->currentDecl, AstType::BREAK, state->tokenStartLocation, state->location);

		next(state);

		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after break", state->lastToken));
			return nullptr;
		}

		return expr;
	}
	else if (state->lastToken == CONTINUE) {
		if (state->forIncrementStack.size() == 0) {
			reportError(state, "Cannot have a break statement outside of a loop");
			return nullptr;
		}

		AstLeafNode *expr = makeLeafNode(state->currentDecl, AstType::CONTINUE, state->tokenStartLocation, state->location);

		next(state);


		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after continue", state->lastToken));
			return nullptr;
		}

		AstNode *increment = state->forIncrementStack[state->forIncrementStack.size() - 1];

		if (increment) { // If we are in a for loop that has an increment expression, execute the increment expression before returning to the top of the loop, @Cleanup: this should probably be in the backend
			AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, expr->startLocation, expr->endLocation, 
				{
					increment, 
					expr
				});

			return sequence;
		}
		else {
			return expr;
		}
	}
	else if (state->lastToken == FOR) {
		return parseForStatement(state);
	}
	else if (state->lastToken == EACH) {
		return parseEachStatement(state);
	}
	else if (state->lastToken == WHILE) {
		return parseWhileStatement(state);
	}
	else if (state->lastToken == RETURN) {
		CodeLocation start = state->tokenStartLocation;

		CodeLocation loc = state->location;

		next(state);

		AstNode *expr;

		if (expectAndConsume(state, SEMICOLON)) {
			if (!(state->currentFunction->flags & DECL_FUNCTION_RETURN_TYPE_IS_KNOWN)) {
				state->currentFunction->flags |= DECL_FUNCTION_RETURN_TYPE_IS_KNOWN | DECL_FUNCTION_IS_VOID;
			}

			if (state->currentFunction->flags & DECL_FUNCTION_IS_VOID) {
				AstLeafNode *ret = makeLeafNode(state->currentDecl, AstType::RETURN, start, state->location);

				return ret;
			}
			else {
				reportError(state, "Function previously returned a value, cannot have mixed return types");
				return nullptr;
			}
		}
		else if (expectAndConsume(state, POUND)) {
			if (!expectAndConsume(state, IF)) {
				reportError(state, expected("Expected if in conditional return", state->lastToken));
				return nullptr;
			}

			expr = parseExpression(state);

			state->currentFunction->flags |= DECL_FUNCTION_RETURN_TYPE_IS_KNOWN;

			if (!expectAndConsume(state, SEMICOLON)) {
				reportError(state, expected("Expected ; after return expression", state->lastToken));
				return nullptr;
			}

			if (state->currentFunction->flags & DECL_FUNCTION_IS_VOID) {
				reportError(state, "Function previously returned void, cannot have mixed return types");
				return nullptr;
			}
			else {
				AstLeafNode *temp = makeLeafNode(state->currentDecl, AstType::VAR_DECL, start, state->location);

				AstTreeNode *sequence = makeTree(state->currentDecl, AstType::SEQUENCE, start, state->location,
					{
						temp,
						makeTree(state->currentDecl, AstType::ASSIGN, start, state->location,
							{
								makeLocalVar(state->currentDecl, temp, start, state->location),
								expr
							}),
						makeTree(state->currentDecl, AstType::IF_ELSE, start, state->location,
							{
								makeLocalVar(state->currentDecl, temp, start, state->location),
								makeTree(state->currentDecl, AstType::RETURN, start, state->location, 
									{
										makeLocalVar(state->currentDecl, temp, start, state->location)
									})
							})
					});

				return sequence;
			}
		}
		else if (expectAndConsume(state, LOGIC_NOT)) {
			if (expectAndConsume(state, POUND)) {
				if (!expectAndConsume(state, IF)) {
					reportError(state, expected("Expected if in conditional return", state->lastToken));
					return nullptr;
				}

				expr = parseExpression(state);

				state->currentFunction->flags |= DECL_FUNCTION_RETURN_TYPE_IS_KNOWN;

				if (!expectAndConsume(state, SEMICOLON)) {
					reportError(state, expected("Expected ; after return expression", state->lastToken));
					return nullptr;
				}

				if (state->currentFunction->flags & DECL_FUNCTION_IS_VOID) {
					reportError(state, "Function previously returned void, cannot have mixed return types");
					return nullptr;
				}
				else {
					AstLeafNode *temp = makeLeafNode(state->currentDecl, AstType::VAR_DECL, start, state->location);

					AstTreeNode *ifElse = makeTree(state->currentDecl, AstType::IF_ELSE, start, state->location,
						{
							expr, 
							makeTree(state->currentDecl, AstType::RETURN, start, state->location,
								{
									makeLiteral(state->currentDecl, 0, start, state->location)
								})
						});

					return ifElse;
				}
			}
			else {
				expr = parseLogicNot(loc, state);
				goto normalReturn;
			}
		}
		else {
			expr = parseExpression(state);
		normalReturn:;

			state->currentFunction->flags |= DECL_FUNCTION_RETURN_TYPE_IS_KNOWN;

			if (!expectAndConsume(state, SEMICOLON)) {
				reportError(state, expected("Expected ; after return expression", state->lastToken));
				return nullptr;
			}

			if (state->currentFunction->flags & DECL_FUNCTION_IS_VOID) {
				reportError(state, "Function previously returned void, cannot have mixed return types");
				return nullptr;
			}
			else {
				AstTreeNode *ret = makeTree(state->currentDecl, AstType::RETURN, start, state->location,
					{
						expr
					});

				return ret;
			}
		}
	}
	else if (state->lastToken == VAR) {
		return parseVarStatement(state);
	}
	else if (state->lastToken == IF) {
		return parseIfStatement(state);
	}
	else if (state->lastToken == SEMICOLON) {
		AstLeafNode *noop = makeLeafNode(state->currentDecl, AstType::NOOP, state->tokenStartLocation, state->location);
		next(state);

		return noop;
	}
	else {
		AstNode *expr = parseExpression(state);

		if (!expr) return nullptr;

		if (!expectAndConsume(state, SEMICOLON)) {
			reportError(state, expected("Expected ; after expression", state->lastToken));
			return nullptr;
		}

		return expr;
	}
}

void printExpression(u32 indentAmount, AstNode *node) {
	for (u32 i = 0; i < 2 * indentAmount; i++) {
		std::cout << " ";
	}

	if (node->flags & AST_IS_TREE) {
		AstTreeNode *tree = static_cast<AstTreeNode *>(node);

		std::cout << astTypeNames[static_cast<u8>(tree->type)] << std::endl;

		for (const auto& child : tree->children) {
			printExpression(indentAmount + 1, child);
		}
	} 
	else {
		AstLeafNode *leaf = static_cast<AstLeafNode *>(node);

		std::cout << astTypeNames[static_cast<u8>(node->type)] << " ";
		switch (node->type) {
			case AstType::LOCAL_VAR:
				if (leaf->localIdent->text.characters) {
					std::cout << leaf->localIdent->text << std::endl;
				}
				else {
					std::cout << static_cast<void *>(leaf->localIdent) << std::endl;
				}
				break;
			case AstType::UNRESOLVED_GLOBAL:
			case AstType::UNRESOLVED_GLOBAL_VAR_ADDRESS:
				std::cout << leaf->text << std::endl;
				break;
			case AstType::GLOBAL_POINTER:
				std::cout << leaf->globalIdent->name << std::endl;
				break;
			case AstType::INT_LITERAL:
				std::cout << leaf->number << std::endl;
				break;
			case AstType::VAR_DECL:
				if (leaf->text.characters) {
					std::cout << leaf->text << std::endl;
				}
				else {
					std::cout << static_cast<void *>(leaf) << std::endl;
				}
				break;
			case AstType::ARGUMENT_DECL:
				std::cout << leaf->text << " " << leaf->unumber << std::endl;
				break;
			case AstType::BREAK:
			case AstType::CONTINUE:
				std::cout << std::endl;
				break;
			default:
				std::cout << "UNKWOWN" << std::endl;
		}
	}
}

static Decl *parseFunctionDecl(LexerState *state) {
	PROFILE_FUNC();
	DeclFunction *decl = new DeclFunction;
	decl->startLocation = state->tokenStartLocation;

	if (!parseModifiers(state, decl)) {
		return nullptr;
	};

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected the function name", state->lastToken));
		return nullptr;
	}

	decl->name = state->lastToken.text;

	next(state);
	state->currentDecl = state->currentFunction = decl;

	if (!expectAndConsume(state, OPEN_PAREN)) {
		reportError(state, expected("Expected ( to start argument list after function name", state->lastToken));
		return nullptr;
	}


	while (!expectAndConsume(state, CLOSE_PAREN)) {
		if (isLocalVar(state->lastToken)) {
			reportError(state, msg("Argument " << state->lastToken.localVar->text << " was already declared at " << state->lastToken.localVar->startLocation << " cannot have multiple arguments with the same name"));
			return nullptr;
		}

		if (!isIdentifier(state->lastToken)) {
			reportError(state, expected("Expected argument name", state->lastToken));
			return nullptr;
		}

		AstLeafNode *node = makeLeafNode(state->currentDecl, AstType::ARGUMENT_DECL, state->tokenStartLocation, state->location);
		node->text = state->lastToken.text;
		node->unumber = static_cast<ulang>(decl->arguments.size());

		decl->arguments.add(node);

		next(state);

		if (!expectAndConsume(state, COMMA)) { // If we get a comma, continue and do the close curly check at the top of the loop to allow trailing comma, otherwise if no comma there must be a close curly following and we break
			if (expectAndConsume(state, CLOSE_PAREN)) {
				break;
			}
			else {
				reportError(state, expected("Expected a , or ) in function argument list", state->lastToken));
				return nullptr;
			}
		}
	}

	decl->endLocation = state->location;

	if (expectAndConsume(state, SEMICOLON)) {
		if (decl->flags & DECL_IS_EXTERN) {
			return decl;
		}
		else {
			reportError(decl, "Function body missing, only extern functions can define no body");
			return nullptr;
		}
	}
	else if (decl->flags & DECL_IS_EXTERN) {
		reportError(state, "Extern function cannot have a body");
		return nullptr;
	}
	else {
		pushScope(state);
		decl->body = parseStatement(state);
		popScope(state);


		if (!decl->body) {
			return nullptr;
		}

		assert(state->currentScopeStackDepth == 0);


		return decl;
	}
}

static DeclVar *parseVarDecl(LexerState *state) {
	PROFILE_FUNC();
	DeclVar *decl = new DeclVar;
	decl->startLocation = state->tokenStartLocation;

	state->currentDecl = decl;

	if (!parseModifiers(state, decl)) {
		return nullptr;
	};

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected the name of a variable", state->lastToken));
		return nullptr;
	}

	decl->name = state->lastToken.text;

	next(state);

	if (expectAndConsume(state, ASSIGN)) {
		if (decl->flags & DECL_IS_EXTERN) {
			reportError(state, "Cannot initialize an extern variable");
			return nullptr;
		}

		decl->value = parseExpression(state);
		if (!decl->value) return nullptr;
	}
	else {
		decl->value = makeLiteral(state->currentDecl, 0, state->tokenStartLocation, state->tokenStartLocation);
	}

	decl->endLocation = state->location;

	if (!expectAndConsume(state, SEMICOLON)) {
		reportError(state, expected("Expected a semicolon after variable declaration", state->lastToken));
		return nullptr;
	}

	return decl;
}

static DeclVar *parseConstDecl(LexerState *state) {
	PROFILE_FUNC();
	DeclVar *decl = new DeclVar;
	decl->type = DeclType::CONST;
	decl->startLocation = state->tokenStartLocation;

	state->currentDecl = decl;

	if (!parseModifiers(state, decl)) {
		return nullptr;
	};

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected the name of a constant", state->lastToken));
		return nullptr;
	}

	decl->name = state->lastToken.text;

	next(state);

	if (expectAndConsume(state, ASSIGN)) {
		if (decl->flags & DECL_IS_EXTERN) {
			reportError(state, "Cannot assign an extern constant");
			return nullptr;
		}

		decl->value = parseExpression(state);
		if (!decl->value) return nullptr;
	}
	else {
		if (!(decl->flags & DECL_IS_EXTERN)) {
			reportError(state, "Must assign a value to a constant");
			return nullptr;
		}
	}

	decl->endLocation = state->location;

	if (!expectAndConsume(state, SEMICOLON)) {
		reportError(state, expected("Expected a semicolon after constant declaration", state->lastToken));
		return nullptr;
	}

	return decl;
}

static Decl *parseArrayDecl(LexerState *state) {
	PROFILE_FUNC();
	DeclArray *decl = new DeclArray;
	decl->startLocation = state->tokenStartLocation;
	state->currentDecl = decl;

	if (!parseModifiers(state, decl)) {
		return nullptr;
	};

	if (!isIdentifier(state->lastToken)) {
		reportError(state, expected("Expected name of array", state->lastToken));
		return nullptr;
	}

	decl->name = state->lastToken.text;

	next(state);

	if (!expectAndConsume(state, OPEN_SQUARE)) {
		reportError(state, expected("Expected [ after array name", state->lastToken));
		return nullptr;
	}

	decl->exprs = nullptr;
	decl->count = 0;

	if (expectAndConsume(state, CLOSE_SQUARE)) {
		decl->exprCount = nullptr;
	}
	else {
		decl->exprCount = parseExpression(state);

		if (!decl->exprCount) return nullptr;

		if (!expectAndConsume(state, CLOSE_SQUARE)) {
			reportError(state, expected("Expected ] after array length", state->lastToken));
		}
	}

	if (state->lastToken == ASSIGN) {
		if (decl->flags & DECL_IS_EXTERN) {
			reportError(state, "Cannot initialize an extern array");
			return nullptr;
		}

		next(state);

		if (!expectAndConsume(state, OPEN_CURLY)) {
			reportError(state, expected("Expected an array initializer", state->lastToken));
			return nullptr;
		}

		Array<AstNode *> values;

		while (!expectAndConsume(state, CLOSE_CURLY)) {
			AstNode *expr = parseExpression(state);
			if (!expr) 
				return nullptr;

			values.add(expr);

			if (!expectAndConsume(state, COMMA)) { // If we get a comma, continue and do the close curly check at the top of the loop to allow trailing comma, otherwise if no comma there must be a close curly following and we break
				if (expectAndConsume(state, CLOSE_CURLY)) {
					break;
				}
				else {
					reportError(state, expected("Expected , or } in array initializer", state->lastToken));
					return nullptr;
				}
			}
		}

		decl->exprs = values.storage;
		decl->count = static_cast<ulang>(values.size());

		if (!decl->exprCount) {
			decl->exprCount = makeLiteral(state->currentDecl, static_cast<slang>(values.size()), decl->startLocation, state->location);
		}
	}
	else if (!decl->exprCount && !(decl->flags & DECL_IS_EXTERN)) { // Allow no size to be specified if the array is extern
		reportError(decl, "Could not determine the size of the array as no size was given");
		return nullptr;
	}


	decl->endLocation = state->location;

	if (!expectAndConsume(state, SEMICOLON)) {
		reportError(state, expected("Expected ; after array declaration", state->lastToken));
		return nullptr;
	}


	return decl;
}

static bool parseLoad(LexerState *state) {
	CodeLocation startLocation = state->tokenStartLocation;
	next(state);

	if (!isStringLiteral(state->lastToken)) {
		reportError(state, expected("Expected string literal name in file load", state->lastToken));
		return false;
	}

	for (u32 i = 0; i < state->lastToken.text.length; i++) {
		if (state->lastToken.text.characters[i] == 0) {
			reportError(state, "Load file name cannot contain a \\0 character");
			return false;
		}

#ifdef _WIN32
		else if (state->lastToken.text.characters[i] == '/') state->lastToken.text.characters[i] = '\\';
#else
		else if (state->lastToken.text.characters[i] == '\\') state->lastToken.text.characters[i] = '/';
#endif
	}

	char *string = toCString(state->lastToken.text);

	if (!addBuildFileFromLoad(string, startLocation, state->location)) {
		return false;
	}

	state->lastToken.text.free(); // We need to free the memory allocated by the lexer to store the string literal since it won't be needed	

	next(state);
	return true;
}

static bool parseFile(LexerState *state) {
	next(state);

	while (state->lastToken != END_OF_FILE) {
		if (state->lastToken == VAR) {
			Decl *decl = parseVarDecl(state);
			if (!decl) return false;

			state->currentDecl = nullptr;

			resolverQueue.add(decl);
		}
		else if (state->lastToken == CONST) {
			Decl *decl = parseConstDecl(state);
			if (!decl) return false;

			state->currentDecl = nullptr;

			resolverQueue.add(decl);
		}
		else if (state->lastToken == ARRAY) {
			Decl *decl = parseArrayDecl(state);
			if (!decl) return false;

			state->currentDecl = nullptr;

			resolverQueue.add(decl);
		}
		else if (state->lastToken == FUNCTION) {
			Decl *decl = parseFunctionDecl(state);
			if (!decl) return false;

			state->currentDecl = state->currentFunction = nullptr;

			resolverQueue.add(decl);
		}
		else if (state->lastToken == LOAD) {
			if (!parseLoad(state)) return false;
		}
		else if (state->lastToken == SEMICOLON) {
			next(state);
		}
		else if (state->lastToken == LOCAL) {
			reportError(state, "Unexpected modifier local, modifiers should be placed after the declaration type");
			return false;
		}
		else if (state->lastToken == EXTERN) {
			reportError(state, "Unexpected modifier extern, modifiers should be placed after the declaration type");
			return false;
		}
		else {
			reportError(state, expected("Expected declaration or load directive", state->lastToken));
			return false;
		}
	}

	return true;
}

bool lexAndParse(const char *filePath, u32 fileUid) {
	PROFILE_FUNC();
	
	LexerState state;
	state.handle = CreateFileA(filePath, GENERIC_READ, 0, 0, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, 0); // @Platform

	if (state.handle == INVALID_HANDLE_VALUE) {
		reportError(msg("Failed to open file: " << filePath));
		return false;
	}

	state.tokenStartLocation.fileUid = fileUid;
	state.location.fileUid = fileUid;
	state.location.line = 1;
	state.location.column = 1;

	bool result = parseFile(&state);

	CloseHandle(state.handle); // @Platform

	completeFile();

	return result;
}

