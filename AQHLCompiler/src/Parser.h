#pragma once

#include "Basic.h"
#include "String.h"
#include "Ast.h"
#include "WorkQueue.h"

struct ParseJob {
	const char *buildFile;
	u32 fileUid;
};

extern u64 NUM_PARSER_THREADS;

extern WorkQueue<ParseJob> parserQueue;

bool lexAndParse(FILE *f, u32 fileUid);

void initLexer();

void runParser();
