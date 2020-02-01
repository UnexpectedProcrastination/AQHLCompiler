#pragma once

#include "WorkQueue.h"
#include "Ast.h"
#include "Array.h"

struct Constraint {
	ulang min;
	ulang max;
};

using Constraints = SmallArray<Constraint, 2>;
extern u64 NUM_OPTIMIZER_THREADS;

extern WorkQueue<DeclFunction *> optimizerQueue;

void runOptimizer();

u64 getRequiredLiveRangeInfoSize(DeclFunction *function);

void calculateLiveRanges(DeclFunction *function, u64 *bits);
void calculateLeaders(DeclFunction *function);

void calculateConstraints(DeclFunction *function, Constraints *constraints);