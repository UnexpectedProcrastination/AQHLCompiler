#pragma once

#include "WorkQueue.h"
#include "Ast.h"

extern WorkQueue<Decl *> codeGenQueue;

void runCodeGen();