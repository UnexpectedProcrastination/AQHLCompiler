#include "Basic.h"
#include "CompilerMain.h"
#include "ArraySet.h"
#include "String.h"
#include "Parser.h"
#include "Resolver.h"
#include "Optimizer.h"
#include "CodeGenerator.h"
#include "BlockWriter.h"
#include <chrono>


#if PROFILE
#include <fstream>
#endif

u32 maxBracktrackCountForComplexConstraints = 0;

static std::mutex fileUidToNameMapMutex;
static Array<const char *> fileUidToNameMap;

// This function allocates a new string
static String stripFileName(const char *file) {
	const char *dir = strrchr(file, '\\');

	dir = dir ? dir + 1 : file;

	const char *extension = strrchr(dir, '.');

	if (extension) {
		return String(dir, extension);
	}
	else {
		return String(dir);
	}

}

Array<const char *> buildFiles;
std::mutex buildFilesMutex;
ulang stackSize = 256;
bool outputIr = false;
bool outputSymbols = false;
std::ofstream symbolOutput;
std::ofstream irOutput;

bool validateName(String filename) {
	for (u32 i = 0; i < filename.length; i++) {
		char c = filename.characters[i];

		if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (i > 0 && c >= '0' && c <= '9') || c == '_') {
			continue;
		}
		return false;
	}

	return true;
}

static ArraySet<String> buildFileNames;

bool addBuildFile(const char *file, bool silent = false) {
	static std::mutex buildFileNamesMutex;

	if (!PathFileExistsA(file)) { // @Platform
		if (silent) {
			return false;
		}
		else {
			reportError(msg(file << " doesn't exist"));
			return false;
		}
	}
	else if (PathIsDirectoryA(file)) { // @Platform
		if (silent) {
			return false;
		}
		else {
			reportError(msg(file << " is a directory"));
			return false;
		}
	}

	String name = stripFileName(file);

	bool added;

	{
		Scope_Lock lock(buildFileNamesMutex);

		added = buildFileNames.add(name);
	}

	if (added) {
		Scope_Lock lock(buildFilesMutex);

		buildFiles.add(file);
	}
	else {
		name.free();
	}

	return true;
}

static char *modulePath = nullptr;
static u64 modulePathLength;

bool addBuildFileFromLoad(const char *file, CodeLocation startLocation, EndLocation endLocation) {
	PROFILE_FUNC();

	if (!addBuildFile(file, false)) {
		char *buffer = new char[modulePathLength + 9 /* length of \modules\ */ + strlen(file) + 1];
		buffer[0] = 0;

		strcat(buffer, modulePath);
		strcat(buffer, "\\modules\\");
		strcat(buffer, file);

		if (!addBuildFile(buffer, false)) {
			reportError(startLocation, endLocation, msg("Could not find file: " << file));
			return false;
		}

		delete[] buffer;
		return true;

	}
	return true;
}

volatile bool hadErrors = false;

const char *getFilename(u32 fileUid) {
	Scope_Lock lock(fileUidToNameMapMutex);

	return fileUidToNameMap[fileUid];
}

volatile u32 filesCompleted = 0;

void completeFile() {
	Scope_Lock lock(buildFilesMutex);
	filesCompleted++;
}

bool fileMap = false;

char *output = nullptr;

#if _WIN32
bool doColorPrint = false;
#else
bool doColorPrint = true;
#endif

static std::mutex outputMutex;

static ArraySet<u64> disabledWarnings;

static void reset() {
	disabledWarnings.clear();
	buildFiles.clear();
	buildFileNames.clear();

	parserQueue.clear();
	resolverQueue.clear();
	optimizerQueue.clear();
	codeGenQueue.clear();
	blockWriterQueue.clear();
	fileUidToNameMap.clear();

	resetCodeGen();
	resetResolver();

	filesCompleted = 0;
}


int main(int argc, char *argv[]) {
#if PROFILE
	u64 startTime;
	QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&startTime));
#endif

	auto t1 = std::chrono::high_resolution_clock::now();
	{
		PROFILE_FUNC();

		PROFILE_START("Initialize");

#if _WIN32
		{
			DWORD size = 256;

			do {
				size *= 2;
				modulePath = static_cast<char *>(realloc(modulePath, size + 1)); // Do we acutally need to add 1 here?
				modulePathLength = GetModuleFileNameA(NULL, modulePath, size) - 1; // The return value includes the null terminator, but we want the length to look like strlen
			} while (GetLastError() == ERROR_INSUFFICIENT_BUFFER);

			*strrchr(modulePath, '\\') = 0;
		}

		HANDLE console = GetStdHandle(STD_OUTPUT_HANDLE);
		if (console != INVALID_HANDLE_VALUE) {
			DWORD mode;

			if (GetConsoleMode(console, &mode)) {
				if (SetConsoleMode(console, mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING)) {
					doColorPrint = true;
				}
			}
		}
#endif

		bool serialCompilation = false;
		float parserThreadsPerOptimizerThread = 4;

		int cursor = 1;

		char *input = 0;

		while (cursor < argc) {
			if (strcmp(argv[cursor], "-stackSize") == 0) {
				++cursor;
				char *end;

				s64 value = strtol(argv[cursor], &end, 0);

				if (*end) {
					std::cerr << "Argument passed to stack size (" << argv[cursor] << ") was not an integer" << std::endl;
					return 1;
				}

				if (value < 0 || value >= 0xFFFF) {
					std::cerr << "Stack size must be between 0 and 65535" << std::endl;
					return 1;
				}

				stackSize = static_cast<ulang>(value);
			}
			else if (strcmp(argv[cursor], "-outputIr") == 0) {
				outputIr = true;
			}
			else if (strcmp(argv[cursor], "-outputSymbols") == 0) {
				outputSymbols = true;
			}
			else if (strcmp(argv[cursor], "-disable") == 0) {
				++cursor;

				char *end;

				u64 disable = strtoull(argv[cursor], &end, 10);

				if (end == argv[cursor] || *end || errno == ERANGE) {
					std::cerr << "Invalid warning id to disable" << std::endl;
					return 1;
				}

				disabledWarnings.add(disable);
			}
			else if (strcmp(argv[cursor], "-O1") == 0) {
				optimizationSettings.enableO1();

				parserThreadsPerOptimizerThread = 1;
			}
			else if (strcmp(argv[cursor], "-O2") == 0) {
				optimizationSettings.enableO2();

				parserThreadsPerOptimizerThread = 1;
			}
			else if (strcmp(argv[cursor], "-fileMap") == 0) {
				fileMap = true;
			}
			else if (strcmp(argv[cursor], "-serial") == 0) { // @Improvement: this option is still not deterministic as strings, and vars/arrays skip certain compilation stages so may arrive at code generation out of order, this only guarantees that all strings are consistently ordered to other strings, all arrays/vars are consistently ordered to arrays/vars and all functions ordered to other functions
				serialCompilation = true;
			}
			else {
				if (*argv[cursor] == '-') {
					std::cerr << "Unkown option: " << argv[cursor] << std::endl;
					return 1;
				}

				for (char *s = argv[cursor]; *s; ++s) {
#if _WIN32
					if (*s == '/')
						*s = '\\';
#else
					if (*s == '\\')
						*s = '/';
#endif
				}

				char *extension = strrchr(argv[cursor], '.');

				if (!*extension) {
					std::cerr << "File specified did not have an extension, couldn't determine if it was the input or output" << std::endl; // @Improvement Maybe default to input?
					return 1;
				}

				++extension;

				if (strcmp(extension, "aqhl") == 0) {
					if (input) {
						std::cerr << "Cannot specify multiple input files" << std::endl;
						return 1;
					}

					input = argv[cursor];
				}
				else if (strcmp(extension, "aq") == 0) {
					if (output) {
						std::cerr << "Cannot specify multiple output files" << std::endl;
						return 1;
					}

					output = argv[cursor];
				}


			}

			++cursor;
		}

		if (serialCompilation) {
			NUM_OPTIMIZER_THREADS = 1;
			NUM_PARSER_THREADS = 1;
		}
		else {
			u64 remainingThreads = std::thread::hardware_concurrency() - 4; // This thread the resolver thread, the codegen thread and the block writer

			NUM_OPTIMIZER_THREADS = (u64) (remainingThreads / (parserThreadsPerOptimizerThread + 1.0f));
			NUM_PARSER_THREADS = (u64) (remainingThreads / (parserThreadsPerOptimizerThread + 1.0f) * parserThreadsPerOptimizerThread);

			/*NUM_OPTIMIZER_THREADS = remainingThreads - 1;
			NUM_PARSER_THREADS = 1;*/

			/*NUM_OPTIMIZER_THREADS = 8;
			NUM_PARSER_THREADS = 1;*/
		}

		if (!input) {
			std::cerr << "Input wasn't specified" << std::endl;
			return 1;
		}

		if (!output) {
			u64 length = strlen(input);
			output = new char[length - 1]; // Allocate enough space for the string minus the 'hl' at the end, plus a null terminator
										   // @Leak this memory is never freed but is needed till the end of the program anyway
			assert(length >= 2);

			memcpy(output, input, length - 2);
			output[length - 2] = 0;
		}

		if (outputSymbols) {
			std::string name(output);
			name = name.append(".symbols");

			symbolOutput.open(name, std::ios::out | std::ios::trunc);
		}

		if (outputIr) {
			std::string name(output);
			name = name.append(".ir");

			irOutput.open(name, std::ios::out | std::ios::trunc);
		}


		if (PathIsDirectoryA(output)) { // @Platform
			std::cerr << "The output is a directory" << std::endl;
			return 1;
		}

		PROFILE_END();

#define ITERATIONS 1

		for (u32 aaa = 0; aaa < ITERATIONS; aaa++) {
			if (!addBuildFile(input)) {
				return 1;
			}

			initLexer();

			PROFILE_START("Launch threads");
			for (u32 i = 0; i < NUM_PARSER_THREADS; i++) {
				std::thread parseThread(runParser);
				parseThread.detach();
			}

			std::thread resolverThread(runResolver);
			resolverThread.detach();


			for (u32 i = 0; i < NUM_OPTIMIZER_THREADS; ++i) {
				std::thread optimizerThread(runOptimizer);
				optimizerThread.detach();
			}

			std::thread codeGenThread(runCodeGen);

			codeGenThread.detach();

			std::thread blockWriterThread(runBlockWriter);
			PROFILE_END();

			u32 fileUid = 0;

			while (true) {
				if (hadErrors) break;

				Scope_Lock lock(buildFilesMutex);

				if (filesCompleted == buildFiles.size()) {
					break;
				}

				while (fileUid < buildFiles.size()) {
					String name = stripFileName(buildFiles[fileUid]);
					const char *cString = toCString(name);
					name.free();

					{
						Scope_Lock lock(fileUidToNameMapMutex);

						fileUidToNameMap.add(cString);
					}


					parserQueue.add({ buildFiles[fileUid], fileUid });

					fileUid++;
				}
			}

			parserQueue.add({ nullptr, 0 });

			blockWriterThread.join();

			if (aaa != ITERATIONS - 1) {
				reset();
			}
		}
	}
	auto t2 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1);

	{
		Scope_Lock lock(outputMutex);
		std::cout << "It took me " << time_span.count() << " seconds." << std::endl;
	}

#if PROFILE
	{
		std::ofstream out("profile.json", std::ios::out | std::ios::trunc);

		u64 pcf;
		QueryPerformanceFrequency(reinterpret_cast<LARGE_INTEGER *>(&pcf));

		out << '[';
		for (u32 i = 0; i < static_cast<u32>(profileIndex); i++) {
			Profile p = profiles[i];

			out << "{\"cat\":\"function\",\"pid\":0,\"tid\":" << p.threadId << ",\"ts\":" << ((p.time - startTime) * 1.0e9 / (double) pcf);

			if (p.name) {
				out << ",\"ph\":\"B\",\"name\":\"" << p.name;

				if (p.data) {
					out << "\",\"args\":{\"data\":\"" << p.data << "\"}}";
				}
				else {
					out << "\"}";
				}
			}
			else {
				out << ",\"ph\":\"E\"}";
			}

			if (i != static_cast<u32>(profileIndex) - 1) {
				out << ",\n";
			}

		}

		out << ']';
	}

#endif

#if BUILD_DEBUG
	std::cin.get();
#endif
}

#if PROFILE
Profile profiles[10000000];
std::atomic_uint32_t profileIndex;
#endif


OptimizationSettings::OptimizationSettings() {
	advancedOptimizations = false;
	deleteRedundantBranches = false;
	advancedThreadJumps = false;
	comboCompareJumps = false;
	redundantStoreElimination = false;
	propagateConstants = false;
	simplifyConstantExpressions = false;
	copyElision = false;
	moveStatementToUse = false;

	renameRegisters = false;
	coalesceRegisters = false;
	allocateRegisters = false;

	usesAccessInfo = false;
	optimizeFramePointers = false;
}

void OptimizationSettings::enableO1() {
	advancedOptimizations = true;
	deleteRedundantBranches = true;
	advancedThreadJumps = true;
	comboCompareJumps = true;
	redundantStoreElimination = true;
	propagateConstants = true;
	simplifyConstantExpressions = true;
	copyElision = true;
	allocateRegisters = true;
	usesAccessInfo = true;
	optimizeFramePointers = true;
}

void OptimizationSettings::enableO2() {
	enableO1();
	renameRegisters = true;
	coalesceRegisters = true;
	moveStatementToUse = true;
	useConstraints = true;
	stringPacking = true;
	deduplicate = true;
}

OptimizationSettings optimizationSettings;

void reportError(const CodeLocation &startLocation, const EndLocation &endLocation, const char *message, const char *type) {
	reportError(startLocation, message, type); // @ErrorMessage: do something with endLocation
}

void reportError(const LexerState *state, const char *message, const char *type) {
	reportError(state->tokenStartLocation, state->location, message, type);
}

void reportError(const CodeLocation &location, const char *message, const char *type) {
	hadErrors = true;
	Scope_Lock lock(outputMutex);

	if (type) {
		std::cout << location << ' ' << type << ": " << message << std::endl;
	}
	else {
		std::cout << location << ' ' << message << std::endl;
	}
}


void reportError(const Decl *location, const char *message, const char *type) {
	reportError(location->startLocation, location->endLocation, message, type);
}

void reportError(const AstNode *location, const char *message, const char *type) {
	reportError(location->startLocation, location->endLocation, message, type);
}

void reportError(const char *message, const char *type) {
	hadErrors = true;
	Scope_Lock lock(outputMutex);

	if (type) {
		std::cout << type << ": " << message << std::endl;
	}
	else {
		std::cout << message << std::endl;
	}
}

void reportWarning(u64 id, Decl *location, const char *message, const char *type) {
	if (!disabledWarnings.contains(id)) {
		Scope_Lock lock(outputMutex);

		if (type) {
			std::cout << location->startLocation << ' ' << type << '(' << id << "): " << message << std::endl;
		}
		else {
			std::cout << location->startLocation << " (" << id << "): " << message << std::endl;
		}
	}
}

void reportWarning(u64 id, AstNode *location, const char *message, const char *type) {
	if (!disabledWarnings.contains(id)) {
		Scope_Lock lock(outputMutex);

		if (type) {
			std::cout << location->startLocation << ' ' << type << '(' << id << "): " << message << std::endl;
		}
		else {
			std::cout << location->startLocation << " (" << id << "): " << message << std::endl;
		}
	}
}
