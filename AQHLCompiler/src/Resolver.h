#pragma once

#include "Ast.h"
#include "WorkQueue.h"


extern WorkQueue<Decl *> resolverQueue;

void runResolver();