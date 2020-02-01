#pragma once

#include "WorkQueue.h"
#include "Ast.h"

struct WriteJob {
	ulang *values;
	u32 offset;
	u32 count;
};

extern WorkQueue<WriteJob> blockWriterQueue;

void runBlockWriter();