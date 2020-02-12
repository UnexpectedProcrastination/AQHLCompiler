#include "Basic.h"
#include "CodeGenerator.h"
#include "Optimizer.h"
#include "CompilerMain.h"
#include "BlockWriter.h"

#undef OUT
#undef IN

#define INSN(opcode, a, b) (((opcode) << 10) | ((a) << 7) | ((b) << 4))
#define COND_INSN(opcode, a, b, cond)  (((opcode) << 10) | ((a) << 7) | ((b) << 4) | (cond))

#define A 0x0
#define B 0x1
#define C 0x2
#define D 0x3

#define E  0x4
#define FP 0x5
#define SP 0x6
#define IP 0x7

#define ZERO      0x4
#define ONE       0x5
#define MINUS_ONE 0x6
#define IMM       0x7

static constexpr ulang SET_REG_TO_REG = 0x01;
static constexpr ulang PUSH_ARG1 = 0x02;
static constexpr ulang PUSH_ARG2 = 0x03;
static constexpr ulang SET_ARG2_ADDR_TO_ARG1 = 0x04;
static constexpr ulang SET_ARG1_ADDR_TO_ARG2 = 0x05;
static constexpr ulang POP = 0x06;
static constexpr ulang PUSH_SET = 0x07;
static constexpr ulang SET_REG_TO_E = 0x08;
static constexpr ulang SET_REG_TO_FP = 0x09;
static constexpr ulang SET_REG_TO_SP = 0x0A;
static constexpr ulang SET_REG_TO_IP = 0x0B;
static constexpr ulang GET_FLAGS = 0x0C;
static constexpr ulang SET_FRAME_TO_REG = 0x0D;
static constexpr ulang SET_FLAGS = 0x0E;
static constexpr ulang SET_STACK_TO_REG = 0x0F;
static constexpr ulang OUT = 0x10;
static constexpr ulang SWAP_STACK = 0x12;
static constexpr ulang SET_BOOLEAN_PATTERN = 0x14;
static constexpr ulang SWAP_REG = 0x15;
static constexpr ulang QUERY_DEVICE = 0x16;
static constexpr ulang SET_REG_TO_STACK_PRESERVE_FLAGS = 0x17;
static constexpr ulang SET_EQ = 0x18;
static constexpr ulang AND = 0x19;
static constexpr ulang TEST = 0x1A;
static constexpr ulang NAND = 0x1B;
static constexpr ulang OR = 0x1C;
static constexpr ulang NOR = 0x1D;
static constexpr ulang XOR = 0x1E;
static constexpr ulang XNOR = 0x1F;
static constexpr ulang ROTATE_LEFT = 0x20;
static constexpr ulang ROTATE_RIGHT = 0x21;
static constexpr ulang SWAP_MEMORY = 0x22;
static constexpr ulang IN = 0x23;
static constexpr ulang SET_NEQ = 0x24;
static constexpr ulang SET_REG_TO_FRAME = 0x25;
static constexpr ulang SET_REG_TO_STACK = 0x26;
static constexpr ulang SET_ARG1_TO_ARG2_ADDR = 0x27;
static constexpr ulang SHIFT_LEFT = 0x28;
static constexpr ulang SHIFT_LEFT_CARRY = 0x29;
static constexpr ulang SHIFT_RIGHT = 0x2A;
static constexpr ulang SHIFT_RIGHT_CARRY = 0x2B;
static constexpr ulang SHIFT_RIGHT_SIGNED = 0x2C;
static constexpr ulang ADD = 0x38;
static constexpr ulang ADD_CARRY = 0x39;
static constexpr ulang SUB = 0x3A;
static constexpr ulang SUB_BORROW = 0x3B;
static constexpr ulang COMP = 0x3C;
static constexpr ulang SUB_BORROW_REVERSE = 0x3D;
static constexpr ulang SUB_REVERSE = 0x3E;

#define C_UN  0x0
#define C_A   0x1
#define C_AE  0x2
#define C_B   0x3
#define C_BE  0x4
#define C_Z   0x5
#define C_NZ  0x6
#define C_G   0x7
#define C_GE  0x8
#define C_L   0x9
#define C_LE  0xA
#define C_O   0xB
#define C_NO  0xC
#define C_S   0xD
#define C_NS  0xE
#define C_CNZ 0xF

static const ulang reverseConditon[] = {
	0,
	C_B,
	C_BE,
	C_A,
	C_AE,
	C_Z,
	C_NZ,
	C_L,
	C_LE,
	C_G,
	C_GE,
	0,
	0,
	0,
	0,
	0
};

static const ulang oppositeCondition[] = {
	0,
	C_BE,
	C_B,
	C_AE,
	C_A,
	C_NZ,
	C_Z,
	C_LE,
	C_L,
	C_GE,
	C_G,
	C_NO,
	C_O,
	C_NS,
	C_S,
	0
};

constexpr size_t BLOCK_SIZE = 4096 / sizeof(ulang);

static_assert((ULANG_MAX + 1) % BLOCK_SIZE == 0);

static bool blockWritten[(ULANG_MAX + 1) / BLOCK_SIZE];
static u32 substsRemainingInBlock[(ULANG_MAX + 1) / BLOCK_SIZE];

// @Improvement: this is fine for 16 bit compilation but doesn't scale
static ulang program[ULANG_MAX + 1];
static ulang writeIndex;


WorkQueue<Decl *> codeGenQueue;

static void printReg(Reg &reg) {
	switch (reg.type) {
		case RegType::REGISTER:
			irOutput << " R" << reg.unumber;
			break;
		case RegType::STATIC_ADROF:
			irOutput << " S:";
			if (reg.decl->flags & DECL_IS_LOCAL) {
				irOutput << getFilename(reg.decl->startLocation.fileUid) << '$';
			}

			irOutput << reg.decl->name;

			if (reg.number) {
				irOutput << ':' << reg.number;
			}
			break;
		case RegType::IMMEDIATE:
			irOutput << ' ' << reg.number;
			break;
	}
}

static ulang stackLocation;
static ulang entryLocation;

static Array<DeclFunction *> initializers;
static DeclFunction *mainFunc;
static Array<DeclVar *> binaryEndDecl;

static void writePreamble() {
	PROFILE_FUNC();

	program[writeIndex++] = INSN(SET_REG_TO_REG, SP, IMM);
	stackLocation = writeIndex++;
	//if (!optimizationSettings.optimizeFramePointers)
		program[writeIndex++] = INSN(SET_REG_TO_SP, FP, A);

	program[writeIndex++] = INSN(SET_REG_TO_REG, IP, IMM);
	entryLocation = writeIndex++;

	substsRemainingInBlock[0] += 2;
}

static void doSubstitutions(Decl *decl, ulang address) {
	PROFILE_FUNC();

	if (outputSymbols && decl->type != DeclType::STRING) {
		if (decl->flags & DECL_IS_LOCAL) {
			symbolOutput << getFilename(decl->startLocation.fileUid) << '$';
		}

		symbolOutput << decl->name << ':' << address << std::endl;
	}

	decl->flags |= DECL_HAS_BEEN_WRITTEN_TO_BINARY;

	decl->locationInBinary = address;

	for (ulang subst : decl->relocations) {
		--substsRemainingInBlock[subst / BLOCK_SIZE];
		program[subst] += address;
	}

	decl->relocations.free();
}

static Array<DeclString *> stringsToWrite;
static Array<DeclString *> otherStrings;

static void writeStringToProgram(DeclString *string) {
	doSubstitutions(string, writeIndex);

	for (u32 i = 0; i < string->name.length; i++) {
		program[writeIndex++] = static_cast<ulang>(string->name.characters[i]);
	}

	program[writeIndex++] = 0;
}

static void writePostamble() {
	PROFILE_FUNC();

	if (optimizationSettings.stringPacking) {
		for (DeclString *string : stringsToWrite) {
			writeStringToProgram(string);
		}

		for (DeclString *string : otherStrings) {
			DeclString *s = string;

			while (s->parent) {
				string->locationInBinary += s->parent->locationInBinary;

				s = s->parent;
			}

			doSubstitutions(string, string->locationInBinary);
		}
	}

	program[entryLocation] = writeIndex;
	--substsRemainingInBlock[0];

	for (DeclFunction *init : initializers) {
		assert(init->flags & DECL_HAS_BEEN_WRITTEN_TO_BINARY);

		program[writeIndex++] = INSN(PUSH_SET, IP, IMM);
		program[writeIndex++] = init->locationInBinary;
	}

	if (mainFunc) {
		assert(mainFunc->flags & DECL_HAS_BEEN_WRITTEN_TO_BINARY);

		program[writeIndex++] = INSN(PUSH_SET, IP, IMM);
		program[writeIndex++] = mainFunc->locationInBinary;

		if (!(mainFunc->flags & DECL_FUNCTION_IS_VOID)) {
			program[writeIndex++] = INSN(OUT, A, A); // If Main returns a value output it
		}

		program[writeIndex++] = INSN(SUB, IP, ONE); // Spin forever
	}
	else {
		reportError("No main function was defined");
		// @Improvement: Maybe allow you not to define a main function
	}

	program[stackLocation] = writeIndex;
	--substsRemainingInBlock[0];
	writeIndex += stackSize;


	for (DeclVar *end : binaryEndDecl) {
		doSubstitutions(end, writeIndex);
	}
}

const static String binaryEndName = String("_binaryEnd");
const static String volatileName = String("_volatile");
const static String mainName = String("Main");
const static String initName = String("_Init");

static void writeArray(DeclArray *array) {
	PROFILE_FUNC();
	doSubstitutions(array, writeIndex);

	if (array->values) {
		for (ulang i = 0; i < array->count; i++) {
			program[writeIndex++] = array->values[i];
		}

		free(array->values);
	}
	else {

		writeIndex += array->count;
	}
}

static void writeVar(DeclVar *var) {
	PROFILE_FUNC();
	doSubstitutions(var, writeIndex);

	assert(var->value->type == AstType::INT_LITERAL);

	program[writeIndex++] = static_cast<AstLeafNode *>(var->value)->unumber;
}

static void writeString(DeclString *string) {
	PROFILE_FUNC();

	if (optimizationSettings.stringPacking) {
		for (u32 i = 0; i < stringsToWrite.size(); i++) {
			DeclString *s = stringsToWrite[i];

			if (string->name == s->name) {
				string->parent = s;
				string->locationInBinary = 0;

				if (!outputIr) // Don't free strings if we output ir since they are still referenced when printed out
					string->name.free();
				otherStrings.add(string);

				// std::cout << "Identical strings merged: " << s->name << std::endl;

				return;
			}
			else if (string->name.length > s->name.length) {
				if (memcmp(string->name.characters + string->name.length - s->name.length, s->name.characters, s->name.length) == 0) {

					// std::cout << "Suffixed strings merged: " << s->name << ", " << string->name << std::endl;

					stringsToWrite[i] = string;
					s->parent = string;
					s->locationInBinary = string->name.length - s->name.length;
					if (!outputIr) // Don't free strings if we output ir since they are still referenced when printed out
						s->name.free();
					otherStrings.add(s);

					return;
				}
			}
			else if (string->name.length < s->name.length) {
				if (memcmp(s->name.characters + s->name.length - string->name.length, string->name.characters, string->name.length) == 0) {

					// std::cout << "Suffixed strings merged: " << string->name << ", " << s->name << std::endl;

					string->parent = s;
					string->locationInBinary = s->name.length - string->name.length;
					if (!outputIr) // Don't free strings if we output ir since they are still referenced when printed out
						string->name.free();
					otherStrings.add(string);

					return;
				}
			}
		}

		stringsToWrite.add(string);
	}
	else {
		writeStringToProgram(string);
	}
}

static Array<ulang> irOpAddresses;
static Array<Array<ulang>> irOpSubstitutions;

static u64 *liveRangeInfo = nullptr;
static u64 liveRangeInfoSize = 0;

static ulang frameOffset;
static bool useFrame;

static u32 getLivePhysicalRegisters(DeclFunction *function, u32 opIndex) {
	u64 addressCount = function->largestReg / (sizeof(u64) * CHAR_BIT) + 1;

	u64 *liveIn = liveRangeInfo + (2ULL + opIndex) * addressCount;
	u64 *liveOut = liveIn + addressCount * function->ops.size();

	// Use a 32 bit integer since we definitey don 't need R32-63
	return static_cast<u32>(*liveIn & *liveOut & 0xF); // 0xF is the mask for R0-3, the virtual registers that are mapped to registers A-D
}

static u32 getAllLivePhysicalRegisters(DeclFunction *function, u32 opIndex) {
	u64 addressCount = function->largestReg / (sizeof(u64) * CHAR_BIT) + 1;

	u64 *liveIn = liveRangeInfo + (2ULL + opIndex) * addressCount;
	u64 *liveOut = liveIn + addressCount * function->ops.size();

	// Use a 32 bit integer since we definitey don 't need R32-63
	return static_cast<u32>((*liveIn | *liveOut) & 0xF); // 0xF is the mask for R0-3, the virtual registers that are mapped to registers A-D
}

static u64 isLiveOut(DeclFunction *function, u32 opIndex, ulang reg) {

	u64 addressCount = function->largestReg / (sizeof(u64) * CHAR_BIT) + 1;

	u64 *liveOut = liveRangeInfo + (2ULL + function->ops.size() + opIndex) * addressCount;

	return *liveOut & (1ULL << reg);
}

/*

			if ((number & 0xF) == 0) {
				number = 0;
			}
			else if ((number & 0xF) == 1) {
				number = 1;
			}
			else if ()
*/


static void writeImmediateInsn(ulang opcode, ulang arg1, slang value, ulang condition = C_UN) {
	if (value == 0) {
		program[writeIndex++] = COND_INSN(opcode, arg1, ZERO, condition);
	}
	else if (value == 1) {
		program[writeIndex++] = COND_INSN(opcode, arg1, ONE, condition);
	}
	else if (value == -1) {
		program[writeIndex++] = COND_INSN(opcode, arg1, MINUS_ONE, condition);
	}
	else {
		program[writeIndex++] = COND_INSN(opcode, arg1, IMM, condition);
		program[writeIndex++] = static_cast<ulang>(value);
	}
}

static void writeImmediateInsnForShift(ulang opcode, ulang arg1, slang value, ulang condition = C_UN) {
	value &= 0xF;

	if (value == 0) {
		program[writeIndex++] = COND_INSN(opcode, arg1, ZERO, condition);
	}
	else if (value == 1) {
		program[writeIndex++] = COND_INSN(opcode, arg1, ONE, condition);
	}
	else if (value == 0xF) { // Shift ignores 12 msb so if the bottom 4 bits are supposed to be 0xF, encode using 0xFFFF as the immediate to use a single word instruction
		program[writeIndex++] = COND_INSN(opcode, arg1, MINUS_ONE, condition);
	}
	else {
		program[writeIndex++] = COND_INSN(opcode, arg1, IMM, condition);
		program[writeIndex++] = static_cast<ulang>(value);
	}
}

static void writeGoto(DeclFunction *function, Ir &op, ulang condition) {
	Ir &target = function->ops[op.jumpTarget];

	// Decide if this is a jump to a return if we just output a return instruction instead
	bool writeReturn = !useFrame && // If we use a stack frame we need to generate code to pop off the stack frame
		target.type == IrType::RETURN && // The target must be a return
		(target.regCount == 0 || (target.regs[0].type == RegType::REGISTER && target.regs[0].unumber == 0)); // The target must either be an undefined void return or have the return value already in R0, the calling convention register

	if (writeReturn) {
		program[writeIndex++] = COND_INSN(POP, IP, A, condition);
	}
	else if (op.jumpTarget < irOpAddresses.size()) {
		writeImmediateInsn(SET_REG_TO_REG, IP, irOpAddresses[op.jumpTarget], condition);
	}
	else {
		program[writeIndex++] = COND_INSN(SET_REG_TO_REG, IP, IMM, condition);
		irOpSubstitutions[op.jumpTarget].add(writeIndex++);
	}

}

static ulang getFrameRegister(ulang regNumber) {
	return regNumber - 4 - frameOffset;
}

static void readFrameRegisterToArg1(ulang arg1, ulang regNumber) {
	writeImmediateInsn(SET_REG_TO_FRAME, arg1, getFrameRegister(regNumber));
}

static void readFrameRegisterToE(ulang regNumber) {
	readFrameRegisterToArg1(E, regNumber);
}

static void writeFrameRegisterFromArg1(ulang arg1, ulang regNumber) {
	writeImmediateInsn(SET_FRAME_TO_REG, arg1, getFrameRegister(regNumber));
}

static void writeFrameRegisterFromE(ulang regNumber) {
	writeFrameRegisterFromArg1(E, regNumber);
}

static void writeSubstInsn(ulang opcode, ulang arg1, Reg &subst, ulang condition = C_UN) {
	if (subst.type == RegType::STATIC_ADROF) {
		if (subst.decl->flags & DECL_HAS_BEEN_WRITTEN_TO_BINARY) {
			writeImmediateInsn(opcode, arg1, static_cast<slang>(subst.decl->locationInBinary) + subst.number, condition);
		}
		else {
			program[writeIndex++] = COND_INSN(opcode, arg1, IMM, condition);
			program[writeIndex] = static_cast<ulang>(subst.number); // Write the offset from the symbol we want to substitute to the program where it will have the base address added to it later when the declaration is compiled

			++substsRemainingInBlock[writeIndex / BLOCK_SIZE];
			subst.decl->relocations.add(writeIndex++);
		}
	}
	else {
		writeImmediateInsn(opcode, arg1, subst.number);
	}
}

static void writeSubstInsnForShift(ulang opcode, ulang arg1, Reg &subst, ulang condition = C_UN) {
	if (subst.type == RegType::STATIC_ADROF) {
		if (subst.decl->flags & DECL_HAS_BEEN_WRITTEN_TO_BINARY) {
			writeImmediateInsnForShift(opcode, arg1, static_cast<slang>(subst.decl->locationInBinary) + subst.number, condition);
		}
		else {
			program[writeIndex++] = COND_INSN(opcode, arg1, IMM, condition);
			program[writeIndex] = static_cast<ulang>(subst.number); // Write the offset from the symbol we want to substitute to the program where it will have the base address added to it later when the declaration is compiled

			++substsRemainingInBlock[writeIndex / BLOCK_SIZE];
			subst.decl->relocations.add(writeIndex++);
		}
	}
	else {
		writeImmediateInsnForShift(opcode, arg1, subst.number, condition);
	}
}

static bool opSetsFlags(Ir &op) {
	switch (op.type) {
		case IrType::ADD:
		case IrType::AND:
		case IrType::OR:
		case IrType::XOR:
		case IrType::EQ:
		case IrType::NOT_EQ:
		case IrType::SUB:
		case IrType::LSHIFT:
		case IrType::RSHIFT:
		case IrType::ARSHIFT:
			// Commutative binary, sub and shift only clobbers the flags if all three registers are frame registers
			return op.dest.unumber < 4 || op.regs[0].type != RegType::REGISTER || op.regs[0].unumber < 4 || op.regs[1].type != RegType::REGISTER || op.regs[1].unumber < 4;
		case IrType::NOT:
		case IrType::NEG:
			// Unary operators never clobber the flags
			return true;
		default:
			return false;
	}
}


static void writeIfZOrNz(DeclFunction *function, u32 index, Ir &op, ulang condition) {
	Reg &reg = op.regs[0];

	bool needCompare = !(index >= 1 && !(op.flags & IR_IS_LEADER));

	if (!needCompare) {
		Ir &last = function->ops[index - 1];

		needCompare = !(last.dest == op.regs[0] && opSetsFlags(last));
	}

	if (condition == C_NZ && op.regs[0].type == RegType::REGISTER && op.regs[0].unumber == C) {
		condition = C_CNZ;
		needCompare = false;
	}

	if (needCompare) {
		switch (reg.type) {
			case RegType::REGISTER:
				if (reg.unumber < 4) {
					program[writeIndex++] = INSN(TEST, reg.unumber, reg.unumber); // Use test r, r instead of comp r, 0 so that in future if there are separate execution units than we use the less often used and unit instead of the adder which is about every other instruction
				}
				else {
					readFrameRegisterToE(reg.unumber); // set e, &(fp+r) sets the zero flag so we don't need a test
				}
				break;
			case RegType::STATIC_ADROF:
				writeSubstInsn(SET_REG_TO_REG, E, reg); // set e, IMM doesn't set flags
				program[writeIndex++] = INSN(COMP, E, ZERO); // There is no test e, e so we have to use comp e, 0
				break;
			case RegType::IMMEDIATE:
				assert(false); // This case should be dealt with by one of the basic Ir optimizations that is required for return insurance to work correctly, if we get here there is an  optimizer bug
				return;

		}
	}

	writeGoto(function, op, condition);
}

struct SaveRegister {
	ulang reg;
	bool saved;
};

static SaveRegister findSaveRegister(DeclFunction *function, u32 index, u32 noOverwriteMask = 0) {
	u32 live = getLivePhysicalRegisters(function, index);

	unsigned long firstRegister;

	Ir &op = function->ops[index];

	if (op.dest && op.dest.unumber < 4) {
		noOverwriteMask |= 1 << op.dest.unumber;
	}

	if (op.type == IrType::CALL) {
		for (Reg &reg : op.callRegs) {
			if (reg.type == RegType::REGISTER && reg.unumber < 4) {
				noOverwriteMask |= 1 << reg.unumber;
			}
		}
	}
	else {
		for (ulang reg = 0; reg < op.regCount; reg++) {
			if (op.regs[reg].type == RegType::REGISTER && op.regs[reg].unumber < 4) {
				noOverwriteMask |= 1 << op.regs[reg].unumber;
			}
		}
	}

	// @Platform BitScanForward is msvc
	if (BitScanForward(&firstRegister, ~(live | noOverwriteMask))) {
		if (firstRegister < 4) {
			return { static_cast<ulang>(firstRegister), false };
		}
	}

	if (BitScanForward(&firstRegister, ~noOverwriteMask)) {
		assert(firstRegister < 4);


		return { static_cast<ulang>(firstRegister), true };
	}
	else {
		assert(false);
		return { 0, true };
	}
}

static void saveRegister(SaveRegister reg) {
	if (reg.saved) {
		program[writeIndex++] = INSN(PUSH_ARG1, reg.reg, A);
	}
}

static void saveRegister(SaveRegister reg, ulang newValue) {
	if (reg.saved) {
		program[writeIndex++] = INSN(PUSH_SET, reg.reg, newValue);
	}
	else {
		program[writeIndex++] = INSN(SET_REG_TO_REG, reg.reg, newValue);
	}
}

static void saveRegister(SaveRegister reg, Reg newValue) {
	if (reg.saved) {
		writeSubstInsn(PUSH_SET, reg.reg, newValue);
	}
	else {
		writeSubstInsn(SET_REG_TO_REG, reg.reg, newValue);
	}
}

static void restoreRegister(SaveRegister reg) {
	if (reg.saved) {
		program[writeIndex++] = INSN(POP, reg.reg, A);
	}
}


static void writeIf(DeclFunction *function, u32 index, Ir &op, ulang condition) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (right.type == RegType::IMMEDIATE) {
		switch (condition) {
			case C_G: {
				if (right.number == -1) {
					writeIfZOrNz(function, index, op, C_NS);
					return;
				}
				break;
			}
			case C_LE: {
				if (right.number == -1) {
					writeIfZOrNz(function, index, op, C_S);
					return;
				}
				break;
			}
			case C_L: {
				if (right.number == 0) {
					writeIfZOrNz(function, index, op, C_S);
					return;
				}
				break;
			}
			case C_GE: {
				if (right.number == 0) {
					writeIfZOrNz(function, index, op, C_NS);
					return;
				}
				break;
			}
			case C_A: {
				if (right.unumber == SLANG_MAX) {
					writeIfZOrNz(function, index, op, C_S);
					return;
				}
				break;
			}
			case C_BE: {
				if (right.unumber == SLANG_MAX) {
					writeIfZOrNz(function, index, op, C_NS);
					return;
				}
				break;
			}
			case C_B: {
				if (right.unumber == SLANG_MAX + 1) {
					writeIfZOrNz(function, index, op, C_NS);
					return;
				}
				break;
			}
			case C_AE: {
				if (right.unumber == SLANG_MAX + 1) {
					writeIfZOrNz(function, index, op, C_S);
					return;
				}
				break;
			}				
		}
	}

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (right.unumber < 4) {
				program[writeIndex++] = INSN(COMP, left.unumber, right.unumber);
				writeGoto(function, op, condition);
			}
			else if (left.unumber < 4) {
				readFrameRegisterToE(right.unumber);
				program[writeIndex++] = INSN(COMP, E, left.unumber);
				writeGoto(function, op, reverseConditon[condition]);
			}
			else {
				readFrameRegisterToE(left.unumber);

				auto save = findSaveRegister(function, index);
				saveRegister(save);

				readFrameRegisterToArg1(save.reg, right.unumber);

				program[writeIndex++] = INSN(COMP, E, save.reg);

				restoreRegister(save);

				writeGoto(function, op, condition);
			}
		}
		else {
			if (left.unumber < 4) {
				writeSubstInsn(COMP, left.unumber, right);
				writeGoto(function, op, condition);
			}
			else {
				readFrameRegisterToE(left.unumber);
				writeSubstInsn(COMP, E, right);
				writeGoto(function, op, condition);
			}
		}
	}
	else {
		writeSubstInsn(SET_REG_TO_REG, E, left);
		writeSubstInsn(COMP, E, right);
		writeGoto(function, op, condition);
	}
}


static void writeTest(DeclFunction *function, u32 index, Ir &op, ulang condition) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (right.unumber < 4) {
				program[writeIndex++] = INSN(TEST, left.unumber, right.unumber);
				writeGoto(function, op, condition);
			}
			else if (left.unumber < 4) {
				readFrameRegisterToE(right.unumber);
				program[writeIndex++] = INSN(TEST, E, left.unumber);
				writeGoto(function, op, condition);
			}
			else {
				readFrameRegisterToE(left.unumber);

				auto save = findSaveRegister(function, index);
				saveRegister(save);

				readFrameRegisterToArg1(save.reg, right.unumber);

				program[writeIndex++] = INSN(TEST, E, save.reg);

				restoreRegister(save);

				writeGoto(function, op, condition);
			}
		}
		else {
			if (left.unumber < 4) {
				writeSubstInsn(TEST, left.unumber, right);
				writeGoto(function, op, condition);
			}
			else {
				readFrameRegisterToE(left.unumber);
				writeSubstInsn(TEST, E, right);
				writeGoto(function, op, condition);
			}
		}
	}
	else {
		writeSubstInsn(SET_REG_TO_REG, E, left);
		writeSubstInsn(TEST, E, right);
		writeGoto(function, op, condition);
	}
}

static void writeCommutativeBinary(DeclFunction *function, u32 index, Ir &op, ulang opcode) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (op.dest.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					if (right.unumber < 4) {
						program[writeIndex++] = INSN(opcode, left.unumber, right.unumber);
					}
					else {
						auto save = findSaveRegister(function, index); // We don't need to exclude the dest register because if it's not live than we didn't actually need the result of this operation so if we get garbage it doesn't matter

						if (save.saved) { // If we would have to save a register to the stack, use a different faster encoding
							readFrameRegisterToE(right.unumber);
							program[writeIndex++] = INSN(opcode, E, left.unumber);
							program[writeIndex++] = INSN(SET_REG_TO_E, left.unumber, A);
						}
						else {
							readFrameRegisterToArg1(save.reg, right.unumber);
							program[writeIndex++] = INSN(opcode, left.unumber, save.reg);
						}
					}
				}
				else if (right.unumber == op.dest.unumber) {
					program[writeIndex++] = INSN(opcode, right.unumber, left.unumber);
				}
				else if (right.unumber < 4) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
					program[writeIndex++] = INSN(opcode, op.dest.unumber, right.unumber);
				}
				else if (left.unumber < 4) {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(opcode, E, left.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else {
					auto save = findSaveRegister(function, index);

					if (save.saved) {
						readFrameRegisterToE(left.unumber);
						readFrameRegisterToArg1(op.dest.unumber, right.unumber);

						program[writeIndex++] = INSN(opcode, E, op.dest.unumber);
						program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
					}
					else {
						readFrameRegisterToArg1(op.dest.unumber, left.unumber);
						readFrameRegisterToArg1(save.reg, right.unumber);

						program[writeIndex++] = INSN(opcode, op.dest.unumber, save.reg);
					}
				}
			}
			else {
				if (right.unumber < 4) {
					if (!isLiveOut(function, index, left.unumber)) {
						program[writeIndex++] = INSN(opcode, left.unumber, right.unumber);
						writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
					}
					else if (!isLiveOut(function, index, right.unumber)) {
						program[writeIndex++] = INSN(opcode, right.unumber, left.unumber);
						writeFrameRegisterFromArg1(right.unumber, op.dest.unumber);
					}
					else {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
						program[writeIndex++] = INSN(opcode, E, right.unumber);
						writeFrameRegisterFromE(op.dest.unumber);
					}
				}
				else if (left.unumber < 4) {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(opcode, E, left.unumber);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else {
					readFrameRegisterToE(left.unumber);

					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);
					program[writeIndex++] = INSN(opcode, E, save.reg);
					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save);
				}
			}
		}
		else {
			if (op.dest.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					writeSubstInsn(opcode, left.unumber, right);
				}
				else if (left.unumber < 4) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
					writeSubstInsn(opcode, op.dest.unumber, right);
				}
				else {
					readFrameRegisterToArg1(op.dest.unumber, left.unumber);
					writeSubstInsn(opcode, op.dest.unumber, right);
				}
			}
			else {
				if (left.unumber < 4) {
					if (isLiveOut(function, index, left.unumber)) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
						writeSubstInsn(opcode, E, right);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else {
						writeSubstInsn(opcode, left.unumber, right);
						writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
					}
				}
				else {
					readFrameRegisterToE(left.unumber);
					writeSubstInsn(opcode, E, right);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);
			writeSubstInsn(opcode, op.dest.unumber, right);
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, E, left);
			writeSubstInsn(opcode, E, right);
			writeFrameRegisterFromE(op.dest.unumber);
		}
	}
}

static void writeUnary(DeclFunction *function, u32 index, Ir &op, ulang opcode, ulang arg2) {
	Reg &reg = op.regs[0];

	if (reg.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (op.dest.unumber == reg.unumber) {
				program[writeIndex++] = INSN(opcode, reg.unumber, arg2);
			}
			else if (reg.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, reg.unumber);
				program[writeIndex++] = INSN(opcode, op.dest.unumber, arg2);
			}
			else {
				readFrameRegisterToArg1(op.dest.unumber, reg.unumber);
				program[writeIndex++] = INSN(opcode, op.dest.unumber, arg2);
			}
		}
		else {
			if (reg.unumber < 4) {
				if (isLiveOut(function, index, reg.unumber)) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, E, reg.unumber);
					program[writeIndex++] = INSN(opcode, E, arg2);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else {
					program[writeIndex++] = INSN(opcode, reg.unumber, arg2);
					writeFrameRegisterFromArg1(reg.unumber, op.dest.unumber);
				}
			}
			else {
				readFrameRegisterToE(reg.unumber);
				program[writeIndex++] = INSN(opcode, E, arg2);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, reg);
			program[writeIndex++] = INSN(opcode, op.dest.unumber, arg2);
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, E, reg);
			program[writeIndex++] = INSN(opcode, E, arg2);
			writeFrameRegisterFromE(op.dest.unumber);
		}
	}
}


static void writeCompare(DeclFunction *function, u32 index, Ir &op, ulang condition) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	ulang reverse = reverseConditon[condition];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (op.dest.unumber < 4) {
				if (right.unumber < 4) {
					program[writeIndex++] = INSN(COMP, left.unumber, right.unumber);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, condition);
				}
				else if (left.unumber < 4) {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(COMP, E, left.unumber);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[reverse]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, reverse);
				}
				else {
					readFrameRegisterToE(left.unumber);
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);

					program[writeIndex++] = INSN(COMP, E, op.dest.unumber);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, condition);
				}
			}
			else {
				if (right.unumber < 4) {
					program[writeIndex++] = INSN(COMP, left.unumber, right.unumber);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, condition);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else if (left.unumber < 4) {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(COMP, E, left.unumber);


					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[reverse]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, reverse);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else {
					readFrameRegisterToE(left.unumber);

					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);
					program[writeIndex++] = INSN(COMP, E, save.reg);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, condition);
					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save);
				}
			}
		}
		else {
			if (op.dest.unumber < 4) {
				if (left.unumber < 4) {
					writeSubstInsn(COMP, left.unumber, right);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, condition);
				}
				else {
					readFrameRegisterToE(left.unumber);
					writeSubstInsn(COMP, E, right);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, condition);
				}
			}
			else {
				if (left.unumber < 4) {
					writeSubstInsn(COMP, left.unumber, right);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, condition);
					writeFrameRegisterFromE(op.dest.unumber);

				}
				else {
					readFrameRegisterToE(left.unumber);
					writeSubstInsn(COMP, E, right);

					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[condition]);
					program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, condition);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_REG_TO_REG, E, left);
			writeSubstInsn(COMP, E, right);

			program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ZERO, oppositeCondition[condition]);
			program[writeIndex++] = COND_INSN(SET_REG_TO_REG, op.dest.unumber, ONE, condition);
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, E, left);
			writeSubstInsn(COMP, E, right);

			program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ZERO, oppositeCondition[condition]);
			program[writeIndex++] = COND_INSN(SET_REG_TO_REG, E, ONE, condition);
			writeFrameRegisterFromE(op.dest.unumber);
		}
	}
}


static void writeSet(Ir &op) {
	Reg &reg = op.regs[0];

	if (reg.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (reg.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, reg.unumber);
			}
			else {
				readFrameRegisterToArg1(op.dest.unumber, reg.unumber);
			}
		}
		else {
			if (reg.unumber < 4) {
				writeFrameRegisterFromArg1(reg.unumber, op.dest.unumber);
			}
			else {
				readFrameRegisterToE(reg.unumber);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, reg);
		}
		else if (op.dest.unumber - 4 - frameOffset == 0) {
			writeSubstInsn(SET_ARG1_ADDR_TO_ARG2, FP, reg);
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, E, reg);
			writeFrameRegisterFromE(op.dest.unumber);
		}
	}
}


static void writeReturn(Ir &op) {
	if (op.regCount) {
		Reg &reg = op.regs[0];

		if (reg.type == RegType::REGISTER) {
			if (reg.unumber < 4) {
				if (reg.unumber) { // If the return value is already in A (R0) don't generate a move
					program[writeIndex++] = INSN(SET_REG_TO_REG, A, reg.unumber);
				}
			}
			else {
				readFrameRegisterToArg1(A, reg.unumber);
			}
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, A, reg);
		}
	}

	if (useFrame) {
		if (frameOffset) {
			writeImmediateInsn(SUB, FP, static_cast<slang>(frameOffset));
		}

		program[writeIndex++] = INSN(SET_REG_TO_FP, SP, A);
		program[writeIndex++] = INSN(POP, FP, A);
	}

	program[writeIndex++] = INSN(POP, IP, A);
}


static void writeRead(DeclFunction *function, u32 index, Ir &op) {
	Reg &address = op.regs[0];

	if (address.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (address.unumber < 4) {
				program[writeIndex++] = INSN(SET_ARG1_TO_ARG2_ADDR, op.dest.unumber, address.unumber);
			}
			else {
				readFrameRegisterToArg1(op.dest.unumber, address.unumber);
				program[writeIndex++] = INSN(SET_ARG1_ADDR_TO_ARG2, op.dest.unumber, op.dest.unumber);
			}
		}
		else {
			if (address.unumber < 4) {
				program[writeIndex++] = INSN(SET_ARG1_TO_ARG2_ADDR, E, address.unumber);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				auto save = findSaveRegister(function, index);

				if (save.saved) {
					program[writeIndex++] = INSN(SET_REG_TO_FP, E, A);
					readFrameRegisterToArg1(FP, address.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_FRAME, FP, ZERO);
					program[writeIndex++] = INSN(SWAP_REG, E, FP);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else {
					readFrameRegisterToArg1(save.reg, address.unumber);
					program[writeIndex++] = INSN(SET_ARG1_TO_ARG2_ADDR, E, save.reg);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_ARG1_TO_ARG2_ADDR, op.dest.unumber, address);
		}
		else {
			writeSubstInsn(SET_ARG1_TO_ARG2_ADDR, E, address);
			writeFrameRegisterFromE(op.dest.unumber);
		}
	}
}


static void writeWrite(DeclFunction *function, u32 index, Ir &op) {
	Reg &address = op.regs[0];
	Reg &value = op.regs[1];

	if (address.type == RegType::REGISTER) {
		if (value.type == RegType::REGISTER) {
			if (address.unumber < 4) {
				if (value.unumber < 4) {
					program[writeIndex++] = INSN(SET_ARG2_ADDR_TO_ARG1, value.unumber, address.unumber);
				}
				else {
					readFrameRegisterToE(value.unumber);
					program[writeIndex++] = INSN(SET_ARG2_ADDR_TO_ARG1, E, address.unumber);
				}
			}
			else {
				if (value.unumber < 4) {
					readFrameRegisterToE(address.unumber);
					program[writeIndex++] = INSN(SET_ARG1_ADDR_TO_ARG2, E, value.unumber);
				}
				else {
					auto save = findSaveRegister(function, index);

					saveRegister(save);

					readFrameRegisterToE(address.unumber);
					readFrameRegisterToArg1(save.reg, value.unumber);
					program[writeIndex++] = INSN(SET_ARG1_ADDR_TO_ARG2, E, save.reg);

					restoreRegister(save);
				}
			}
		}
		else {
			if (address.unumber < 4) {
				writeSubstInsn(SET_ARG1_ADDR_TO_ARG2, address.unumber, value);
			}
			else {
				readFrameRegisterToE(address.unumber);
				writeSubstInsn(SET_ARG1_ADDR_TO_ARG2, E, value);
			}
		}
	}
	else {
		if (value.type == RegType::REGISTER) {
			if (value.unumber < 4) {
				writeSubstInsn(SET_ARG2_ADDR_TO_ARG1, value.unumber, address);
			}
			else {
				readFrameRegisterToE(value.unumber);
				writeSubstInsn(SET_ARG2_ADDR_TO_ARG1, E, address);
			}
		}
		else {
			writeSubstInsn(SET_REG_TO_REG, E, value);
			writeSubstInsn(SET_ARG2_ADDR_TO_ARG1, E, address);
		}
	}
}


static void writeShift(DeclFunction *function, u32 index, Ir &op, ulang opcode) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (op.dest.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					if (right.unumber < 4) {
						program[writeIndex++] = INSN(opcode, left.unumber, right.unumber);
					}
					else {
						auto save = findSaveRegister(function, index);

						if (save.saved) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							readFrameRegisterToArg1(left.unumber, right.unumber);
							program[writeIndex++] = INSN(opcode, E, left.unumber);
							program[writeIndex++] = INSN(SET_REG_TO_E, left.unumber, A);
						}
						else {
							readFrameRegisterToArg1(save.reg, right.unumber);

							program[writeIndex++] = INSN(opcode, left.unumber, save.reg);
						}
					}
				}
				else if (right.unumber == op.dest.unumber) {
					if (left.unumber < 4) {
						if (isLiveOut(function, index, left.unumber)) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							program[writeIndex++] = INSN(opcode, E, right.unumber);
							program[writeIndex++] = INSN(SET_REG_TO_E, right.unumber, A);
						}
						else {
							program[writeIndex++] = INSN(opcode, left.unumber, right.unumber);
							program[writeIndex++] = INSN(SET_REG_TO_REG, right.unumber, left.unumber);
						}
					}
					else {
						readFrameRegisterToE(left.unumber);
						program[writeIndex++] = INSN(opcode, E, right.unumber);
						program[writeIndex++] = INSN(SET_REG_TO_E, right.unumber, A);
					}
				}
				else if (left.unumber < 4) {
					if (right.unumber < 4) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
						program[writeIndex++] = INSN(opcode, op.dest.unumber, right.unumber);
					}
					else {
						if (isLiveOut(function, index, left.unumber)) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							readFrameRegisterToArg1(op.dest.unumber, right.unumber);
							program[writeIndex++] = INSN(opcode, E, op.dest.unumber);
							program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
						}
						else {
							program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
							readFrameRegisterToArg1(left.unumber, right.unumber);
							program[writeIndex++] = INSN(opcode, op.dest.unumber, left.unumber);
						}
					}
				}
				else if (right.unumber < 4) {
					readFrameRegisterToArg1(op.dest.unumber, left.unumber);
					program[writeIndex++] = INSN(opcode, op.dest.unumber, right.unumber);
				}
				else {
					readFrameRegisterToE(left.unumber);
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);
					program[writeIndex++] = INSN(opcode, E, op.dest.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
			}
			else {
				if (left.unumber < 4) {
					if (right.unumber < 4) {
						if (isLiveOut(function, index, left.unumber)) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							program[writeIndex++] = INSN(opcode, E, right.unumber);
							writeFrameRegisterFromE(op.dest.unumber);
						}
						else {
							program[writeIndex++] = INSN(opcode, left.unumber, right.unumber);
							writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
						}
					}
					else {
						if (isLiveOut(function, index, left.unumber)) {
							program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							readFrameRegisterToArg1(left.unumber, right.unumber);
							program[writeIndex++] = INSN(opcode, E, left.unumber);
							writeFrameRegisterFromE(op.dest.unumber);
							program[writeIndex++] = INSN(POP, left.unumber, A);
						}
						else {
							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
							readFrameRegisterToArg1(left.unumber, right.unumber);
							program[writeIndex++] = INSN(opcode, E, left.unumber);
							writeFrameRegisterFromE(op.dest.unumber);
						}
					}
				}
				else if (right.unumber < 4) {
					readFrameRegisterToE(left.unumber);
					program[writeIndex++] = INSN(opcode, E, right.unumber);
					writeFrameRegisterFromE(op.dest.unumber);
				}
				else {
					auto save = findSaveRegister(function, index);

					readFrameRegisterToE(left.unumber);

					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);
					program[writeIndex++] = INSN(opcode, E, save.reg);
					restoreRegister(save);

					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
		else {
			if (op.dest.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					writeSubstInsnForShift(opcode, left.unumber, right);
				}
				else if (left.unumber < 4) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
					writeSubstInsnForShift(opcode, op.dest.unumber, right);
				}
				else {
					readFrameRegisterToArg1(op.dest.unumber, left.unumber);
					writeSubstInsnForShift(opcode, op.dest.unumber, right);
				}
			}
			else {
				if (left.unumber < 4) {
					if (isLiveOut(function, index, left.unumber)) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
						writeSubstInsnForShift(opcode, E, right);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else {
						writeSubstInsnForShift(opcode, left.unumber, right);
						writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
					}
				}
				else {
					readFrameRegisterToE(left.unumber);
					writeSubstInsnForShift(opcode, E, right);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
	}
	else {
		if (right.type == RegType::REGISTER) {
			if (op.dest.unumber < 4) {
				if (right.unumber == op.dest.unumber) {
					writeSubstInsn(SET_REG_TO_REG, E, left);
					program[writeIndex++] = INSN(opcode, E, right.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else if (right.unumber < 4) {
					writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);
					program[writeIndex++] = INSN(opcode, op.dest.unumber, right.unumber);
				}
				else {
					writeSubstInsn(SET_REG_TO_REG, E, left);
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);
					program[writeIndex++] = INSN(opcode, E, op.dest.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, left);
				program[writeIndex++] = INSN(opcode, E, right.unumber);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else {
			if (op.dest.unumber < 4) {
				writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);
				writeSubstInsnForShift(opcode, op.dest.unumber, right);
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, left);
				writeSubstInsnForShift(opcode, E, right);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
	}
}


static void writeArray(Ir &op) {
	Reg &size = op.regs[0];

	if (size.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			program[writeIndex++] = INSN(SET_REG_TO_SP, op.dest.unumber, A);
			program[writeIndex++] = INSN(ADD, SP, size.unumber);
		}
		else {
			writeFrameRegisterFromArg1(SP, op.dest.unumber);
			program[writeIndex++] = INSN(ADD, SP, size.unumber);
		}
	}
	else {
		if (op.dest.unumber < 4) {
			program[writeIndex++] = INSN(SET_REG_TO_SP, op.dest.unumber, A);
			writeSubstInsn(ADD, SP, size);
		}
		else {
			writeFrameRegisterFromArg1(SP, op.dest.unumber);
			writeSubstInsn(ADD, SP, size);
		}
	}
}

static u32 shuffleGetPointCount(ulang *registers, ulang reg) {
	u32 total = 0;

	for (u32 i = 0; i < 4; i++) {
		if (registers[i] == reg) ++total;
	}

	return total;
}

static bool shuffleNotDone(ulang *registers, ulang count) {
	for (u32 i = 0; i < count; i++) {
		if (registers[i] != 0xFFFF) return true;
	}

	return false;
}

static Array<ulang> pushRegisters;

static void writeFunctionPostamble() {
	while (pushRegisters.size()) {
		slang decAmt = 0;

		while (pushRegisters.size() && pushRegisters[pushRegisters.size() - 1] == 0xFFFF) {
			pushRegisters.pop();

			decAmt++;
		}

		if (decAmt) {
			writeImmediateInsn(SUB, SP, decAmt);
		}
		else {
			program[writeIndex++] = INSN(POP, pushRegisters.pop(), A);
		}
	}
}

static void writeCall(DeclFunction *function, u32 index, Ir &op) {
	PROFILE_FUNC();


	Reg &call = op.callRegs[0];

	if (call.type == RegType::STATIC_ADROF && call.unumber == 0 && call.decl->name == volatileName) return;

	u32 live = getLivePhysicalRegisters(function, index);

	ulang inRegister = 0xF;

	u32 invalidate = 0;

	for (slang i = static_cast<slang>(pushRegisters.size()) - 1; i >= 0; i--) {
		ulang reg = pushRegisters[i];

		if (reg == 0xFFFF) continue;

		if (live & (1 << reg) && (!op.dest || op.dest.unumber != reg)) {
			inRegister &= ~(1 << reg);
		}
		else {
			if (static_cast<ulang>(i) == pushRegisters.size() - 1) {
				pushRegisters.pop();

				ulang j;
				for (j = 0; j < op.callRegs.size(); j++) {
					if (op.callRegs[j].type == RegType::REGISTER && op.callRegs[j].unumber == reg) {
						program[writeIndex++] = INSN(POP, reg, A);
						break;
					}
				}

				slang decAmt = 0;

				if (j == op.callRegs.size()) {
					++decAmt;
					inRegister &= ~(1 << reg);
				}


				while (pushRegisters.size() && pushRegisters[pushRegisters.size() - 1] == 0xFFFF) {
					pushRegisters.pop();
					decAmt++;
					i--;
				}

				if (decAmt)
					writeImmediateInsn(SUB, SP, decAmt);
			}
			else {
				// @Audit_CallSavedRegistersMadeRedundant Is it always valid to just throw away the save value or do we have to restore it in some situations?

				if (outputSymbols) {
					symbolOutput << "@Audit_CallSavedRegistersMadeRedundant" << writeIndex << ':' << writeIndex << std::endl;
				}

				invalidate |= 1 << i;

				inRegister &= ~(1 << reg);


				/*
				ulang moved = pushRegisters.pop();

				program[writeIndex++] = INSN(POP, reg, A);
				writeImmediateInsn(SWAP_STACK, reg, static_cast<slang>(i - pushRegisters.size()));

				pushRegisters[i] = moved;
				*/
			}
		}
	}

	for (ulang i = 0; i < 4; i++) {
		auto idx = std::find(pushRegisters.begin(), pushRegisters.end(), i);

		if (idx == pushRegisters.end() && live & (1 << i) && (!op.dest || op.dest.unumber != i)) {
			idx = std::find(pushRegisters.begin(), pushRegisters.end(), 0xFFFF);

			if (idx == pushRegisters.end()) {
				program[writeIndex++] = INSN(PUSH_ARG1, i, A);
				pushRegisters.add(i);
			}
			else {
				writeImmediateInsn(SET_STACK_TO_REG, i, static_cast<slang>(idx - pushRegisters.end()));
				*idx = i;
			}
		}
	}

	if (call.type == RegType::REGISTER) {
		if (call.unumber < 4) {
			if (inRegister & (1 << call.unumber)) {
				program[writeIndex++] = INSN(PUSH_ARG1, call.unumber, A);
			}
			else {
				writeImmediateInsn(SET_REG_TO_STACK_PRESERVE_FLAGS, E,
					static_cast<slang>(std::find(pushRegisters.begin(), pushRegisters.end(), call.unumber) - pushRegisters.end()));
				program[writeIndex++] = INSN(PUSH_ARG1, E, A);
			}
		}
		else {
			readFrameRegisterToE(call.unumber);
			program[writeIndex++] = INSN(PUSH_ARG1, E, A);
		}

		for (u32 i = 5; i < op.regCount; i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER) {
				if (arg.unumber < 4) {
					if (!(inRegister & (1 << arg.unumber))) {
						writeImmediateInsn(SET_REG_TO_STACK_PRESERVE_FLAGS, static_cast<ulang>(i - 1),
							static_cast<slang>(std::find(pushRegisters.begin(), pushRegisters.end(), arg.unumber) - pushRegisters.end() - 1));

						inRegister |= 1 << arg.unumber;
					}

					writeImmediateInsn(SET_STACK_TO_REG, arg.unumber, static_cast<slang>(i - 4));
				}
				else {
					readFrameRegisterToE(arg.unumber);
					writeImmediateInsn(SET_STACK_TO_REG, E, static_cast<slang>(i - 4));
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, arg);
				writeImmediateInsn(SET_STACK_TO_REG, E, static_cast<slang>(i - 4));
			}
		}


		ulang registers[4] = { 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF };

		for (u32 i = 1; i < my_min(op.regCount, 5u); i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER && arg.unumber < 4 && arg.unumber != i - 1 && (inRegister & (1 << arg.unumber))) {
				registers[i - 1] = arg.unumber;
			}
		}

		while (shuffleNotDone(registers, 4)) {
			for (ulang i = 0; i < 4; i++) {
				if (registers[i] != -1) {
					u32 pointCount = shuffleGetPointCount(registers, i);

					if (pointCount == 0) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, i, registers[i]);
						registers[i] = 0xFFFF;
					}
					else if (pointCount == 1) {
						if (shuffleGetPointCount(registers, registers[i]) == 1) {
							program[writeIndex++] = INSN(SWAP_REG, i, registers[i]);

							for (u32 j = 0; j < 4; j++) {
								if (registers[j] == i) {
									registers[j] = registers[i] == j ? 0xFFFF : registers[i];
								}
							}

							registers[i] = 0xFFFF;
						}
					}
				}
			}
		}


		for (ulang i = 1; i < my_min(op.regCount, 5u); i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER) {
				if (arg.unumber >= 4) {
					readFrameRegisterToArg1(i - 1, arg.unumber);
				}
				else if (!(inRegister & (1 << arg.unumber))) {
					ulang j;

					for (j = 1; j < i; j++) {
						if (op.callRegs[j] == arg) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, i - 1, j - 1);
							break;
						}
					}

					if (j == i) {
						writeImmediateInsn(SET_REG_TO_STACK_PRESERVE_FLAGS, i - 1,
							static_cast<slang>(std::find(pushRegisters.begin(), pushRegisters.end(), arg.unumber) - pushRegisters.end() - 1));
					}
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, i - 1, arg);
			}
		}

		program[writeIndex++] = INSN(SWAP_STACK, IP, MINUS_ONE);
	}
	else {
		for (u32 i = 5; i < op.regCount; i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER) {
				if (arg.unumber < 4) {
					if (!(inRegister & (1 << arg.unumber))) {
						writeImmediateInsn(SET_REG_TO_STACK_PRESERVE_FLAGS, static_cast<ulang>(i - 1),
							static_cast<slang>(std::find(pushRegisters.begin(), pushRegisters.end(), arg.unumber) - pushRegisters.end()));

						inRegister |= 1 << arg.unumber;
					}

					writeImmediateInsn(SET_STACK_TO_REG, arg.unumber, static_cast<slang>(i - 4));
				}
				else {
					readFrameRegisterToE(arg.unumber);
					writeImmediateInsn(SET_STACK_TO_REG, E, static_cast<slang>(i - 4));
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, arg);
				writeImmediateInsn(SET_STACK_TO_REG, E, static_cast<slang>(i - 4));
			}
		}


		ulang registers[4] = { 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF };

		for (ulang i = 1; i < my_min(op.regCount, 5u); i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER && arg.unumber < 4 && arg.unumber != i - 1 && (inRegister & (1 << arg.unumber))) {
				registers[i - 1] = arg.unumber;
			}
		}

		while (shuffleNotDone(registers, 4)) {
			for (ulang i = 0; i < 4; i++) {
				if (registers[i] != 0xFFFF) {
					u32 pointCount = shuffleGetPointCount(registers, i);

					if (pointCount == 0) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, i, registers[i]);
						registers[i] = 0xFFFF;
					}
					else if (pointCount == 1) {
						if (shuffleGetPointCount(registers, registers[i]) == 1) {
							program[writeIndex++] = INSN(SWAP_REG, i, registers[i]);

							for (u32 j = 0; j < 4; j++) {
								if (registers[j] == i) {
									registers[j] = registers[i] == j ? 0xFFFF : registers[i];
								}
							}

							registers[i] = 0xFFFF;
						}
					}
				}
			}
		}


		for (ulang i = 1; i < my_min(op.regCount, 5); i++) {
			Reg &arg = op.callRegs[i];

			if (arg.type == RegType::REGISTER) {
				if (arg.unumber >= 4) {
					readFrameRegisterToArg1(i - 1, arg.unumber);
				}
				else if (!(inRegister & (1 << arg.unumber))) {
					ulang j = 1;

					for (j = 1; j < i; j++) {
						if (op.callRegs[j] == arg) {
							program[writeIndex++] = INSN(SET_REG_TO_REG, i - 1, j - 1);
							break;
						}
					}

					if (j == i) {
						writeImmediateInsn(SET_REG_TO_STACK_PRESERVE_FLAGS, i - 1,
							static_cast<slang>(std::find(pushRegisters.begin(), pushRegisters.end(), arg.unumber) - pushRegisters.end()));
					}
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, i - 1, arg);
			}
		}

		writeSubstInsn(PUSH_SET, IP, call);
	}

	if (op.dest && op.dest.unumber) {
		if (op.dest.unumber < 4) {
			program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, A);
		}
		else {
			writeFrameRegisterFromArg1(A, op.dest.unumber);
		}
	}


	for (u32 bits = invalidate; bits; bits = _blsr_u64(bits)) {
		unsigned long idx;
		BitScanForward(&idx, bits);

		pushRegisters[idx] = 0xFFFF;
	}

	op.callRegs.free();
}


static void writeSub(DeclFunction *function, u32 index, Ir &op) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (left.unumber < 4 && right.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					program[writeIndex++] = INSN(SUB, left.unumber, right.unumber);
				}
				else if (right.unumber == op.dest.unumber) {
					program[writeIndex++] = INSN(SUB_REVERSE, right.unumber, left.unumber);
				}
				else if (op.dest.unumber < 4) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
					program[writeIndex++] = INSN(SUB, op.dest.unumber, right.unumber);
				}
				else {
					if (!isLiveOut(function, index, left.unumber)) {
						program[writeIndex++] = INSN(SUB, left.unumber, right.unumber);
						writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
					}
					else if (!isLiveOut(function, index, right.unumber)) {
						program[writeIndex++] = INSN(SUB, right.unumber, left.unumber);
						writeFrameRegisterFromArg1(right.unumber, op.dest.unumber);
					}
					else {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
						program[writeIndex++] = INSN(SUB, E, right.unumber);
						writeFrameRegisterFromE(op.dest.unumber);
					}
				}
			}
			else if (left.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(SUB_REVERSE, E, left.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else if (op.dest.unumber < 4) {
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);
					program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, left.unumber);
				}
				else {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(SUB_REVERSE, E, left.unumber);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
			else if (right.unumber < 4) {
				if (right.unumber == op.dest.unumber) {
					readFrameRegisterToE(left.unumber);
					program[writeIndex++] = INSN(SUB, E, right.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else if (op.dest.unumber < 4) {
					readFrameRegisterToArg1(op.dest.unumber, left.unumber);
					program[writeIndex++] = INSN(SUB, op.dest.unumber, right.unumber);
				}
				else {
					readFrameRegisterToE(left.unumber);
					program[writeIndex++] = INSN(SUB, E, right.unumber);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
			else {
				if (op.dest.unumber < 4) {
					readFrameRegisterToE(left.unumber);
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);
					program[writeIndex++] = INSN(SUB, E, op.dest.unumber);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else {
					auto save = findSaveRegister(function, index);

					readFrameRegisterToE(left.unumber);
					saveRegister(save);
					readFrameRegisterToArg1(save.reg, right.unumber);
					program[writeIndex++] = INSN(SUB, E, save.reg);
					restoreRegister(save);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
		else {
			if (left.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					writeSubstInsn(SUB, left.unumber, right);
				}
				else if (op.dest.unumber < 4) {
					program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
					writeSubstInsn(SUB, op.dest.unumber, right);
				}
				else {
					if (isLiveOut(function, index, left.unumber)) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
						writeSubstInsn(SUB, E, right);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else {
						writeSubstInsn(SUB, left.unumber, right);
						writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
					}
				}
			}
			else {
				if (op.dest.unumber < 4) {
					readFrameRegisterToArg1(op.dest.unumber, left.unumber);
					writeSubstInsn(SUB, op.dest.unumber, right);
				}
				else {
					readFrameRegisterToE(left.unumber);
					writeSubstInsn(SUB, E, right);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
	}
	else {
		if (right.type == RegType::REGISTER) {
			if (right.unumber < 4) {
				if (right.unumber == op.dest.unumber) {
					writeSubstInsn(SUB_REVERSE, op.dest.unumber, left);
				}
				else if (op.dest.unumber < 4) {
					writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);
					program[writeIndex++] = INSN(SUB, op.dest.unumber, right);
				}
				else {
					writeSubstInsn(SET_REG_TO_REG, E, left);
					program[writeIndex++] = INSN(SUB, E, right);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
			else {
				if (op.dest.unumber < 4) {
					readFrameRegisterToArg1(op.dest.unumber, right.unumber);
					program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, left);
				}
				else {
					readFrameRegisterToE(right.unumber);
					program[writeIndex++] = INSN(SUB_REVERSE, E, left);
					writeFrameRegisterFromE(op.dest.unumber);
				}
			}
		}
		else {
			if (op.dest.unumber < 4) {
				writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);
				writeSubstInsn(SUB, op.dest.unumber, right);
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, left);
				writeSubstInsn(SUB, E, right);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
	}
}

static void outputMultiply(ulang dest, ulang arg1, ulang arg2) {
	program[writeIndex++] = INSN(SET_REG_TO_REG, dest, ZERO);

	program[writeIndex++] = INSN(COMP, arg1, ZERO);
	program[writeIndex++] = COND_INSN(SET_REG_TO_REG, dest, arg2, C_S);

	program[writeIndex++] = INSN(SHIFT_LEFT, dest, ONE);
	program[writeIndex++] = INSN(ROTATE_LEFT, arg1, ONE);

	for (u32 i = 0; i < 15; i++) { // @WordSize
		program[writeIndex++] = COND_INSN(ADD, dest, arg2, C_S);

		if (i != 14) {
			program[writeIndex++] = INSN(SHIFT_LEFT, dest, ONE);
		}

		program[writeIndex++] = INSN(ROTATE_LEFT, arg1, ONE);

	}
}

static slang stripLeadingOnes(ulang *newValue, u32 *newIndex) {
	slang count = 1;

	ulang value = *newValue;


	unsigned long lastIndex;

	BitScanReverse(&lastIndex, value);

	unsigned long saveIndex = lastIndex;

	value &= ~(1 << lastIndex);

	ulang saveValue = value;

	while (value) {
		unsigned long index;

		BitScanReverse(&index, value);

		if (index + 1 != lastIndex) break;

		value &= ~(1 << index);
		++count;

		lastIndex = index;
	}


	if (count <= 2) { // It isn't actually faster to strip two at a time
		*newIndex = saveIndex;
		*newValue = saveValue;

		return 1;
	}

	*newIndex = lastIndex;
	*newValue = value;

	return count;
}

static void outputConstantMultiplyImpl(ulang dest, ulang arg2, ulang constant) {
	u32 lastIndex;

	program[writeIndex++] = INSN(SET_REG_TO_REG, dest, arg2);

	slang leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
	if (leadingOneCount >= 3) {
		writeImmediateInsn(SHIFT_LEFT, dest, leadingOneCount);
		program[writeIndex++] = INSN(SUB, dest, arg2);
	}

	while (constant) {
		unsigned long index;
		unsigned long idx = lastIndex;

		BitScanReverse(&index, constant);



		leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
		if (leadingOneCount >= 3) {
			if (idx - index - 1) {
				writeImmediateInsn(SHIFT_LEFT, dest, static_cast<slang>(idx - index - 1));
			}

			program[writeIndex++] = INSN(ADD, dest, arg2);

			writeImmediateInsn(SHIFT_LEFT, dest, leadingOneCount);
			program[writeIndex++] = INSN(SUB, dest, arg2);
		}
		else {
			writeImmediateInsn(SHIFT_LEFT, dest, static_cast<slang>(idx - index));

			program[writeIndex++] = INSN(ADD, dest, arg2);
		}
	}

	if (lastIndex) {
		writeImmediateInsn(SHIFT_LEFT, dest, static_cast<slang>(lastIndex));
	}
}

static u32 getCostForConstantMultiply(ulang constant) {
	u32 cost = 0;

	u32 lastIndex;

	++cost; //  program[writeIndex++] = INSN(SET_REG_TO_REG, dest, arg2);

	slang leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
	if (leadingOneCount >= 3) {
		cost += 2; //  writeImmediateInsn(SHIFT_LEFT, dest, leadingOneCount);
		++cost; //  writeImmediateInsn(SUB, dest, arg2);
	}

	while (constant) {
		unsigned long index;

		BitScanReverse(&index, constant);

		++cost;
		if (lastIndex - index != 1) ++cost; // 		writeImmediateInsn(SHIFT_LEFT, dest, lastIndex - index);

		++cost; // 		program[writeIndex++] = INSN(ADD, dest, arg2);

		leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
		if (leadingOneCount >= 3) {
			cost += 2; //  writeImmediateInsn(SHIFT_LEFT, dest, leadingOneCount);
			++cost; //  writeImmediateInsn(SUB, dest, arg2);
		}
	}

	if (lastIndex) {
		++cost;
		if (lastIndex != 1) ++cost; // 		writeImmediateInsn(SHIFT_LEFT, dest, lastIndex);
	}

	return cost;
}

static void outputConstantMultiply(ulang dest, ulang arg2, ulang constant) {
	if (getCostForConstantMultiply(constant) <= getCostForConstantMultiply(-constant) + 1) {
		outputConstantMultiplyImpl(dest, arg2, constant);
	}
	else {
		outputConstantMultiplyImpl(dest, arg2, -constant);
		program[writeIndex++] = INSN(SUB_REVERSE, dest, ZERO);
	}
}

static void writeMul(DeclFunction *function, u32 index, Ir &op) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER) {
		if (right.type == RegType::REGISTER) {
			if (op.dest.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					if (right.unumber < 4) {
						if (right.unumber == left.unumber) {
							auto save = findSaveRegister(function, index);
							saveRegister(save, right.unumber);

							outputMultiply(E, left.unumber, save.reg);

							program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

							restoreRegister(save);
						}
						else {
							outputMultiply(E, left.unumber, right.unumber);

							program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
						}
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, right.unumber);
						outputMultiply(E, left.unumber, save.reg);

						program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

						restoreRegister(save);
					}
				}
				else if (right.unumber == op.dest.unumber) {
					outputMultiply(E, left.unumber, right.unumber);

					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
				}
				else if (right.unumber < 4) {
					if (right.unumber == left.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);

						outputMultiply(op.dest.unumber, E, right.unumber);
					}
					else {
						outputMultiply(op.dest, left.unumber, right.unumber);
					}
				}
				else if (left.unumber < 4) {
					readFrameRegisterToE(right.unumber);

					outputMultiply(op.dest.unumber, E, left.unumber);
				}
				else {
					readFrameRegisterToE(left.unumber);

					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);
					outputMultiply(op.dest.unumber, E, save.reg);

					restoreRegister(save);
				}
			}
			else {
				if (right.unumber < 4) {
					if (right.unumber == left.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save, right.unumber);

						outputMultiply(E, left.unumber, save.reg);

						writeFrameRegisterFromE(op.dest.unumber);

						restoreRegister(save);
					}
					else {
						outputMultiply(E, left.unumber, right.unumber);

						writeFrameRegisterFromE(op.dest.unumber);
					}
				}
				else if (left.unumber < 4) {
					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);

					outputMultiply(E, left.unumber, save.reg);

					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save);
				}
				else {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1);

					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2);

					readFrameRegisterToArg1(save1.reg, left.unumber);
					readFrameRegisterToArg1(save2.reg, right.unumber);

					outputMultiply(E, save1.reg, save2.reg);

					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save2);
					restoreRegister(save1);
				}
			}
		}
		else {
			if (right.type == RegType::IMMEDIATE) {
				if (op.dest.unumber < 4) {
					if (right.number == 0) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
					}
					else if (left.unumber == op.dest.unumber) {
						if ((right.number & (right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, right.number);

							if (idx) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}
						}
						else if ((-right.number & (-right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, -right.number);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}

							program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
						}
						else {
							outputConstantMultiply(E, left.unumber, right.number);
							program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
						}
					}
					else if (left.unumber < 4) {
						if ((right.number & (right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, right.number);

							program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}
						}
						else if ((-right.number & (-right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, -right.number);

							program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}

							program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
						}
						else {
							outputConstantMultiply(op.dest.unumber, left.unumber, right.number);
						}
					}
					else {
						if ((right.number & (right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, right.number);

							readFrameRegisterToArg1(op.dest.unumber, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}
						}
						else if ((-right.number & (-right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, -right.number);

							readFrameRegisterToArg1(op.dest.unumber, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
							}

							program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
						}
						else {
							readFrameRegisterToArg1(op.dest.unumber, left.unumber);

							outputConstantMultiply(E, op.dest.unumber, right.number);

							program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
						}
					}
				}
				else {
					if (right.number == 0) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else if (left.unumber < 4) {
						if ((right.number & (right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, right.number);

							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
							}

							writeFrameRegisterFromE(op.dest.unumber);
						}
						else if ((-right.number & (-right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, -right.number);

							program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
							}

							program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
							writeFrameRegisterFromE(op.dest.unumber);
						}
						else {
							outputConstantMultiply(E, left.unumber, right.number);
							writeFrameRegisterFromE(op.dest.unumber);
						}
					}
					else {
						if ((right.number & (right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, right.number);

							readFrameRegisterToE(left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
							}

							writeFrameRegisterFromE(op.dest.unumber);
						}
						else if ((-right.number & (-right.number - 1)) == 0) {
							unsigned long idx;

							BitScanForward(&idx, -right.number);

							readFrameRegisterToE(left.unumber);

							if (index) {
								writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
							}

							program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
							writeFrameRegisterFromE(op.dest.unumber);
						}
						else {
							auto save = findSaveRegister(function, index);
							saveRegister(save);

							readFrameRegisterToArg1(save.reg, left.unumber);

							outputConstantMultiply(E, save.reg, right.number);
							writeFrameRegisterFromE(op.dest.unumber);

							restoreRegister(save);
						}
					}
				}
			}
			else {
				if (op.dest.unumber < 4) {
					if (left.unumber == op.dest.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save, left.unumber);

						writeSubstInsn(SET_REG_TO_REG, E, right);

						outputMultiply(op.dest.unumber, E, save.reg);

						restoreRegister(save);
					}
					else if (left.unumber < 4) {
						writeSubstInsn(SET_REG_TO_REG, E, right);
						outputMultiply(op.dest.unumber, E, left.unumber);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, left.unumber);
						writeSubstInsn(SET_REG_TO_REG, E, right);

						outputMultiply(op.dest.unumber, E, save.reg);

						restoreRegister(save);
					}
				}
				else {
					if (left.unumber < 4) {
						auto save = findSaveRegister(function, index);
						saveRegister(save, right);

						writeSubstInsn(SET_REG_TO_REG, save.reg, right);

						outputMultiply(E, left.unumber, save.reg);

						restoreRegister(save);
					}
					else {
						auto save1 = findSaveRegister(function, index);
						saveRegister(save1);

						auto save2 = findSaveRegister(function, index, 1 << save1.reg);
						saveRegister(save2, right);

						readFrameRegisterToArg1(save1.reg, left.unumber);

						outputMultiply(E, save1.reg, save2.reg);

						writeFrameRegisterFromE(op.dest.unumber);

						restoreRegister(save2);
						restoreRegister(save1);
					}
				}
			}
		}
	}
	else if (right.type == RegType::IMMEDIATE) {
		if (op.dest.unumber < 4) {
			if (right.number == 0) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
			}
			else if ((right.number & (right.number - 1)) == 0) {
				unsigned long idx;

				BitScanForward(&idx, right.number);

				writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);

				if (index) {
					writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
				}
			}
			else if ((-right.number & (-right.number - 1)) == 0) {
				unsigned long idx;

				BitScanForward(&idx, -right.number);

				writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);

				if (index) {
					writeImmediateInsnForShift(SHIFT_LEFT, op.dest.unumber, static_cast<slang>(idx));
				}

				program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, op.dest.unumber, left);

				outputConstantMultiply(E, op.dest.unumber, right.number);
				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
			}
		}
		else {
			if (right.number == 0) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else if ((right.number & (right.number - 1)) == 0) {
				unsigned long idx;

				BitScanForward(&idx, right.number);

				writeSubstInsn(SET_REG_TO_REG, E, left);

				if (index) {
					writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
				}

				writeFrameRegisterFromE(op.dest.unumber);
			}
			else if ((-right.number & (-right.number - 1)) == 0) {
				unsigned long idx;

				BitScanForward(&idx, -right.number);

				writeSubstInsn(SET_REG_TO_REG, E, left);

				if (index) {
					writeImmediateInsnForShift(SHIFT_LEFT, E, static_cast<slang>(idx));
				}

				program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				auto save = findSaveRegister(function, index);
				saveRegister(save, left);

				outputConstantMultiply(E, save.reg, right.number);
				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save);
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			auto save = findSaveRegister(function, index);
			saveRegister(save, right);

			writeSubstInsn(SET_REG_TO_REG, E, left);

			outputMultiply(op.dest.unumber, E, save.reg);

			restoreRegister(save);
		}
		else {
			auto save1 = findSaveRegister(function, index);
			saveRegister(save1, left);

			auto save2 = findSaveRegister(function, index, 1 << save1.reg);
			saveRegister(save2, right);

			outputMultiply(E, save1.reg, save2.reg);

			writeFrameRegisterFromE(op.dest.unumber);

			restoreRegister(save2);
			restoreRegister(save1);
		}
	}
}

static void outputDivide(ulang quotientReg, ulang remainderReg, ulang arg1, ulang arg2, bool setQuotientToZero = true) {
	if (setQuotientToZero)
		program[writeIndex++] = INSN(SET_REG_TO_REG, quotientReg, ZERO);

	program[writeIndex++] = INSN(SET_REG_TO_REG, remainderReg, ZERO);

	program[writeIndex++] = INSN(XOR, arg1, arg2);
	program[writeIndex++] = INSN(PUSH_ARG1, arg1, A);
	program[writeIndex++] = INSN(XOR, arg1, arg2);

	program[writeIndex++] = COND_INSN(SUB_REVERSE, arg1, ZERO, C_S);
	program[writeIndex++] = INSN(TEST, arg2, arg2);
	program[writeIndex++] = COND_INSN(SUB_REVERSE, arg2, ZERO, C_S);

	writeImmediateInsn(SHIFT_LEFT, arg1, 2);


	for (u32 i = 0; i < 15; i++) {// @WordSize
		if (i != 0) {
			program[writeIndex++] = INSN(SHIFT_LEFT, quotientReg, 1);
			program[writeIndex++] = INSN(SHIFT_LEFT, arg1, ONE);
		}

		program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, remainderReg, ONE);
		program[writeIndex++] = INSN(SUB, remainderReg, arg2);
		program[writeIndex++] = COND_INSN(OR, quotientReg, ONE, C_NS);
		program[writeIndex++] = COND_INSN(ADD, remainderReg, arg2, C_S);
	}

	program[writeIndex++] = INSN(POP, arg1, A);
	program[writeIndex++] = INSN(COMP, arg1, ZERO);
	program[writeIndex++] = COND_INSN(SUB_REVERSE, quotientReg, ZERO, C_S);
}

static ulang getDivideConstants(ulang divisor, ulang *shift) {
	unsigned long index;
	BitScanReverse(&index, divisor);

	*shift = index + 1;

	u64 low = (1ULL << (16 + *shift)) / divisor; // @WordSize
	u64 high = ((1ULL << (16 + *shift)) + (1ULL << (1 + *shift))) / divisor;

	while ((low >> 1) < (high >> 1) && *shift > 0) {
		low >>= 1;
		high >>= 1;
		--(*shift);
	}

	return static_cast<ulang>(high);
}

static void outputMulHigh(ulang dest, ulang sign, ulang low, ulang arg2, ulang constant) {
	u32 lastIndex;
	program[writeIndex++] = INSN(SHIFT_RIGHT_SIGNED, sign, MINUS_ONE);

	program[writeIndex++] = INSN(SET_REG_TO_REG, dest, sign);

	slang leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
	if (leadingOneCount >= 3) {
		for (slang i = 0; i < leadingOneCount; i++) {
			program[writeIndex++] = INSN(SHIFT_LEFT, low, ONE);
			program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, dest, ONE);
		}

		program[writeIndex++] = INSN(SUB, low, arg2);
		program[writeIndex++] = INSN(SUB_BORROW, dest, sign);
	}

	while (constant) {
		unsigned long index;
		unsigned long idx = lastIndex;

		BitScanReverse(&index, constant);

		leadingOneCount = stripLeadingOnes(&constant, &lastIndex);
		if (leadingOneCount >= 3) {
			for (u32 i = 1; i < idx - index; i++) {
				program[writeIndex++] = INSN(SHIFT_LEFT, low, ONE);
				program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, dest, ONE);
			}

			program[writeIndex++] = INSN(ADD, low, arg2);
			program[writeIndex++] = INSN(ADD_CARRY, dest, sign);

			for (slang i = 0; i < leadingOneCount; i++) {
				program[writeIndex++] = INSN(SHIFT_LEFT, low, ONE);
				program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, dest, ONE);
			}

			program[writeIndex++] = INSN(SUB, low, arg2);
			program[writeIndex++] = INSN(SUB_BORROW, dest, sign);
		}
		else {
			for (u32 i = 0; i < idx - index; i++) {
				program[writeIndex++] = INSN(SHIFT_LEFT, low, ONE);
				program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, dest, ONE);
			}

			program[writeIndex++] = INSN(ADD, low, arg2);
			program[writeIndex++] = INSN(ADD_CARRY, dest, sign);
		}
	}

	for (u32 i = 0; i < lastIndex; i++) { // In theory constant should always be odd when we are doing this for a constant divide, but this is trivial cost, so is kept in case this function is used for something other than constant divide
		program[writeIndex++] = INSN(SHIFT_LEFT, low, ONE);
		program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, dest, ONE);
	}
}

static void outputConstantDivide(ulang dest, ulang sign, ulang low, ulang arg2, slang num) {
	ulang shift;
	u64 mult = getDivideConstants(static_cast<ulang>(num < 0 ? -num : num), &shift);

	if (mult < (1 << 15)) { // @WordSize
		outputMulHigh(dest, sign, low, arg2, static_cast<ulang>(mult));

		if (shift) {
			writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, dest, shift);
		}
		
		program[writeIndex++] = INSN(SUB, dest, sign);
	}
	else {
		outputMulHigh(dest, sign, low, arg2, static_cast<ulang>((1 << 16) - mult)); // @WordSize

		program[writeIndex++] = INSN(SUB_REVERSE, low, ZERO);
		program[writeIndex++] = INSN(SUB_BORROW_REVERSE, dest, arg2);

		if (shift) {
			writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, dest, shift);
		}

		program[writeIndex++] = INSN(SUB, dest, sign);
	}

	if (num < 0) {
		program[writeIndex++] = INSN(SUB_REVERSE, dest, ZERO);
	}
}

static void outputConstantMod(ulang dest, ulang sign, ulang low, ulang arg2, slang num) {
	outputConstantDivide(dest, sign, low, arg2, num);

	if (dest == E) {
		program[writeIndex++] = INSN(SET_REG_TO_E, sign, A);
	}
	else {
		program[writeIndex++] = INSN(SET_REG_TO_REG, sign, dest);
	}

	outputConstantMultiply(dest, sign, num);
	program[writeIndex++] = INSN(SUB_REVERSE, dest, arg2);
}

static void writeDiv(DeclFunction *function, u32 index, Ir &op) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER && right.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (left.unumber < 4) {
				if (right.unumber < 4) {
					if (left.unumber == op.dest.unumber && right.unumber == op.dest.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ONE);
					}
					else if (left.unumber == op.dest.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save, left.unumber);

						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputDivide(op.dest.unumber, E, save.reg, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);

						restoreRegister(save);
					}
					else if (right.unumber == op.dest.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save, right.unumber);

						program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);

						outputDivide(op.dest.unumber, E, left.unumber, save.reg);

						program[writeIndex++] = INSN(POP, left.unumber, A);

						restoreRegister(save);
					}
					else {
						program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);
						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputDivide(op.dest.unumber, E, left.unumber, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);
						program[writeIndex++] = INSN(POP, left.unumber, A);
					}
				}
				else {
					if (left.unumber == op.dest.unumber) {
						auto save1 = findSaveRegister(function, index);
						saveRegister(save1, left.unumber);
						auto save2 = findSaveRegister(function, index, 1 << save1.reg);
						saveRegister(save2);

						readFrameRegisterToArg1(save2.reg, right.unumber);

						outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

						restoreRegister(save2);
						restoreRegister(save1);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, right.unumber);

						program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);

						outputDivide(op.dest.unumber, E, left.unumber, save.reg);

						program[writeIndex++] = INSN(POP, left.unumber, A);

						restoreRegister(save);
					}
				}
			}
			else { // left.unumber >= 4
				if (right.unumber < 4) {
					if (right.unumber == op.dest.unumber) {
						auto save1 = findSaveRegister(function, index);
						saveRegister(save1);
						auto save2 = findSaveRegister(function, index, 1 << save1.reg);
						saveRegister(save2, right.unumber);

						readFrameRegisterToArg1(save1.reg, left.unumber);

						outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

						restoreRegister(save2);
						restoreRegister(save1);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, left.unumber);

						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputDivide(op.dest.unumber, E, save.reg, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);

						restoreRegister(save);
					}
				}
				else {
					if (right.unumber == left.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ONE);
					}
					else {
						auto save1 = findSaveRegister(function, index);
						saveRegister(save1);
						auto save2 = findSaveRegister(function, index, 1 << save1.reg);
						saveRegister(save2);

						readFrameRegisterToArg1(save1.reg, left.unumber);
						readFrameRegisterToArg1(save2.reg, right.unumber);

						outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

						restoreRegister(save2);
						restoreRegister(save1);
					}
				}
			}
		}
		else { // op.dest.unumnber >= 4
			if (left.unumber < 4) {
				if (right.unumber < 4) {
					if (right.unumber == left.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, ONE);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save, ZERO);

						program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);
						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputDivide(save.reg, E, left.unumber, right.unumber, false);

						program[writeIndex++] = INSN(POP, right.unumber, A);
						program[writeIndex++] = INSN(POP, left.unumber, A);

						writeFrameRegisterFromArg1(save.reg, op.dest.unumber);

						restoreRegister(save);
					}
				}
				else {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, ZERO);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2);

					readFrameRegisterToArg1(save2.reg, right.unumber);

					program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);

					outputDivide(save1.reg, E, left.unumber, save2.reg, false);

					program[writeIndex++] = INSN(POP, left.unumber, A);


					writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

					restoreRegister(save2);
					restoreRegister(save1);
				}
			}
			else { // left.unumber >= 4, op.dest.unumber >= 4
				if (right.unumber < 4) {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, ZERO);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2);

					readFrameRegisterToArg1(save2.reg, left.unumber);

					program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

					outputDivide(save1.reg, E, save2.reg, right.unumber, false);

					program[writeIndex++] = INSN(POP, right.unumber, A);


					writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

					restoreRegister(save2);
					restoreRegister(save1);
				}
				else {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, ZERO);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2);
					auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
					saveRegister(save3);

					readFrameRegisterToArg1(save2.reg, left.unumber);
					readFrameRegisterToArg1(save3.reg, right.unumber);

					outputDivide(save1.reg, E, save2.reg, save3.reg, false);


					writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

					restoreRegister(save3);
					restoreRegister(save2);
					restoreRegister(save1);
				}
			}
		}
	}
	else if (left.type == RegType::REGISTER && right.type == RegType::IMMEDIATE) {
		if (right.unumber == 0) {
			if (op.dest.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
			}
			else {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if (right.unumber == 1) {
			if (left.unumber == op.dest.unumber) {

			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
			}
			else if (left.unumber < 4) {
				writeFrameRegisterFromArg1(left.unumber, op.dest.unumber);
			}
			else {
				readFrameRegisterToE(left.unumber);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if (right.number == -1) {
			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				program[writeIndex++] = INSN(SUB_REVERSE, left.unumber, ZERO);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
			}
			else if (left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
				program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				readFrameRegisterToE(left.unumber);
				program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if ((right.unumber & (right.unumber - 1)) == 0) {
			unsigned long idx;
			BitScanForward(&idx, right.unumber);

			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				program[writeIndex++] = INSN(TEST, left.unumber, left.unumber);
				writeImmediateInsn(ADD, left.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, left.unumber, idx);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(TEST, op.dest.unumber, op.dest.unumber);
				writeImmediateInsn(ADD, op.dest.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, op.dest.unumber, idx);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				writeImmediateInsn(ADD, op.dest.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, op.dest.unumber, idx);
			}
			else if (left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
				program[writeIndex++] = INSN(COMP, E, 0);
				writeImmediateInsn(ADD, E, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, E, idx);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				readFrameRegisterToE(left.unumber);
				writeImmediateInsn(ADD, E, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, E, idx);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if ((-right.unumber & (-right.unumber - 1)) == 0) {
			unsigned long idx;
			BitScanForward(&idx, right.unumber);

			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				program[writeIndex++] = INSN(TEST, left.unumber, left.unumber);
				writeImmediateInsn(ADD, left.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, left.unumber, idx);
				program[writeIndex++] = INSN(SUB_REVERSE, left.unumber, ZERO);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(TEST, op.dest.unumber, op.dest.unumber);
				writeImmediateInsn(ADD, op.dest.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, op.dest.unumber, idx);
				program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				writeImmediateInsn(ADD, op.dest.unumber, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, op.dest.unumber, idx);
				program[writeIndex++] = INSN(SUB_REVERSE, op.dest.unumber, ZERO);
			}
			else if (left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
				program[writeIndex++] = INSN(COMP, E, 0);
				writeImmediateInsn(ADD, E, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, E, idx);
				program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				readFrameRegisterToE(left.unumber);
				writeImmediateInsn(ADD, E, right.number - 1, C_S);
				writeImmediateInsnForShift(SHIFT_RIGHT_SIGNED, E, idx);
				program[writeIndex++] = INSN(SUB_REVERSE, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else {
			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left.unumber);

				outputConstantDivide(E, save1.reg, save2.reg, left.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				auto save = findSaveRegister(function, index);
				saveRegister(save, left.unumber);
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);

				outputConstantDivide(E, op.dest.unumber, save.reg, left.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, op.dest.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, op.dest.unumber);
				
				outputConstantDivide(E, save1.reg, save2.reg, op.dest.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else if (left.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left.unumber);

				outputConstantDivide(E, save1.reg, save2.reg, left.unumber, right.number);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1);
				readFrameRegisterToArg1(save1.reg, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, save1.reg);
				auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
				saveRegister(save3, save1.reg);

				outputConstantDivide(E, save2.reg, save3.reg, save1.reg, right.number);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save3);
				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else if (left.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (left.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, left.unumber);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2, right);

					outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

					restoreRegister(save2);
					restoreRegister(save1);
				}
				else {
					auto save = findSaveRegister(function, index);
					saveRegister(save, right);

					program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);

					outputDivide(op.dest.unumber, E, left.unumber, save.reg);

					program[writeIndex++] = INSN(POP, left.unumber, A);

					restoreRegister(save);
				}
			}
			else { // left.unumber >= 4
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, right);

				readFrameRegisterToArg1(save1.reg, left.unumber);

				outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
		else {
			if (left.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, ZERO);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, right);

				program[writeIndex++] = INSN(PUSH_ARG1, left.unumber, A);

				outputDivide(save1.reg, E, left.unumber, save2.reg, false);

				program[writeIndex++] = INSN(POP, left.unumber, A);

				writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, ZERO);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2);
				auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
				saveRegister(save3, right);

				readFrameRegisterToArg1(save2.reg, left.unumber);

				outputDivide(save1.reg, E, save2.reg, save3.reg, false);

				writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

				restoreRegister(save3);
				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else if (left.type == RegType::IMMEDIATE && right.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (right.unumber < 4) {
				if (right.unumber == op.dest.unumber) {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, left);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2, right.unumber);

					outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

					restoreRegister(save2);
					restoreRegister(save1);
				}
				else {
					auto save = findSaveRegister(function, index);
					saveRegister(save, left);

					program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

					outputDivide(op.dest.unumber, E, save.reg, right.unumber);

					program[writeIndex++] = INSN(POP, right.unumber, A);

					restoreRegister(save);
				}
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2);

				readFrameRegisterToArg1(save2.reg, right.unumber);

				outputDivide(op.dest.unumber, E, save1.reg, save2.reg);

				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
		else {
			if (right.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, ZERO);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left);

				program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

				outputDivide(save1.reg, E, save2.reg, right.unumber, false);

				program[writeIndex++] = INSN(POP, right.unumber, A);

				writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, ZERO);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left);
				auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
				saveRegister(save3);

				readFrameRegisterToArg1(save3.reg, right.unumber);

				outputDivide(save1.reg, E, save2.reg, save3.reg, false);

				writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

				restoreRegister(save3);
				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			auto save1 = findSaveRegister(function, index);
			saveRegister(save1, left);
			auto save2 = findSaveRegister(function, index, 1 << save1.reg);
			saveRegister(save2, right);

			outputDivide(save1.reg, E, save1.reg, save2.reg);

			restoreRegister(save2);
			restoreRegister(save1);
		}
		else {
			auto save1 = findSaveRegister(function, index);
			saveRegister(save1, ZERO);
			auto save2 = findSaveRegister(function, index, 1 << save1.reg);
			saveRegister(save2, left);
			auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
			saveRegister(save3, right);

			outputDivide(save1.reg, E, save2.reg, save3.reg, false);

			writeFrameRegisterFromArg1(save1.reg, op.dest.unumber);

			restoreRegister(save3);
			restoreRegister(save2);
			restoreRegister(save1);
		}
	}
}

static void outputMod(ulang remainderReg, ulang arg1, ulang arg2) {
	program[writeIndex++] = INSN(SET_REG_TO_REG, remainderReg, ZERO);

	program[writeIndex++] = INSN(PUSH_ARG1, arg1, A);

	program[writeIndex++] = COND_INSN(SUB_REVERSE, arg1, ZERO, C_S);
	program[writeIndex++] = INSN(TEST, arg2, arg2);
	program[writeIndex++] = COND_INSN(SUB_REVERSE, arg2, ZERO, C_S);

	writeImmediateInsn(SHIFT_LEFT, arg1, 2);


	for (u32 i = 0; i < 15; i++) {// @WordSize
		if (i != 0) {
			program[writeIndex++] = INSN(SHIFT_LEFT, arg1, ONE);
		}

		program[writeIndex++] = INSN(SHIFT_LEFT_CARRY, remainderReg, ONE);
		program[writeIndex++] = INSN(SUB, remainderReg, arg2);
		program[writeIndex++] = COND_INSN(ADD, remainderReg, arg2, C_S);
	}

	program[writeIndex++] = INSN(POP, arg1, A);
	program[writeIndex++] = INSN(COMP, arg1, ZERO);
	program[writeIndex++] = COND_INSN(SUB_REVERSE, remainderReg, ZERO, C_S);
}

static void writeMod(DeclFunction *function, u32 index, Ir &op) {
	Reg &left = op.regs[0];
	Reg &right = op.regs[1];

	if (left.type == RegType::REGISTER && right.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (left.unumber < 4) {
				if (right.unumber < 4) {
					if (left.unumber == op.dest.unumber && right.unumber == op.dest.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
					}
					else if (left.unumber == op.dest.unumber) {
						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputMod(E, left.unumber, right.unumber);
						program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

						program[writeIndex++] = INSN(POP, right.unumber, A);
					}
					else if (right.unumber == op.dest.unumber) {
						outputMod(E, left.unumber, right.unumber);
						program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);
					}
					else {
						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputMod(op.dest.unumber, left.unumber, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);
					}
				}
				else {
					if (left.unumber == op.dest.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, right.unumber);

						outputMod(E, left.unumber, save.reg);
						program[writeIndex++] = INSN(SET_REG_TO_E, E, op.dest.unumber);

						restoreRegister(save);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, right.unumber);

						outputMod(op.dest.unumber, left.unumber, save.reg);

						restoreRegister(save);
					}
				}
			}
			else { // left.unumber >= 4
				if (right.unumber < 4) {
					if (right.unumber == op.dest.unumber) {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToArg1(save.reg, left.unumber);

						outputMod(E, save.reg, right.unumber);
						program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

						restoreRegister(save);
					}
					else {

						readFrameRegisterToE(left.unumber);

						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputMod(op.dest.unumber, E, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);
					}
				}
				else { // left.unumber >= 4, right.unumber >= 4
					if (right.unumber == left.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
					}
					else {
						auto save = findSaveRegister(function, index);
						saveRegister(save);

						readFrameRegisterToE(left.unumber);
						readFrameRegisterToArg1(save.reg, right.unumber);

						outputMod(op.dest.unumber, E, save.reg);

						restoreRegister(save);
					}
				}
			}
		}
		else { // op.dest.unumnber >= 4
			if (left.unumber < 4) {
				if (right.unumber < 4) {
					if (right.unumber == left.unumber) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
						writeFrameRegisterFromE(op.dest.unumber);
					}
					else {
						program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

						outputMod(E, left.unumber, right.unumber);

						program[writeIndex++] = INSN(POP, right.unumber, A);

						writeFrameRegisterFromE(op.dest.unumber);
					}
				}
				else {
					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, right.unumber);

					outputMod(E, left.unumber, save.reg);


					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save);
				}
			}
			else { // left.unumber >= 4, op.dest.unumber >= 4
				if (right.unumber < 4) {
					auto save = findSaveRegister(function, index);
					saveRegister(save);

					readFrameRegisterToArg1(save.reg, left.unumber);

					program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

					outputMod(E, save.reg, right.unumber);

					program[writeIndex++] = INSN(POP, right.unumber, A);


					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save);
				}
				else {
					auto save1 = findSaveRegister(function, index);
					saveRegister(save1, ZERO);
					auto save2 = findSaveRegister(function, index, 1 << save1.reg);
					saveRegister(save2);

					readFrameRegisterToArg1(save1.reg, left.unumber);
					readFrameRegisterToArg1(save2.reg, right.unumber);

					outputMod(E, save1.reg, save2.reg);


					writeFrameRegisterFromE(op.dest.unumber);

					restoreRegister(save2);
					restoreRegister(save1);
				}
			}
		}
	}
	else if (left.type == RegType::REGISTER && right.type == RegType::IMMEDIATE) {
		slang num = right.number < 0 ? -right.number : right.number;

		if (num == 0) {
			if (op.dest.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
			}
			else {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if (num == 1) {
			if (op.dest.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, ZERO);
			}
			else {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, ZERO);
				writeFrameRegisterFromE(op.dest.unumber);
			}
		}
		else if ((num & (num - 1)) == 0) {
			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
				program[writeIndex++] = INSN(TEST, left.unumber, left.unumber);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, left.unumber, ZERO, C_S);
				writeImmediateInsn(AND, left.unumber, num - 1);
				program[writeIndex++] = INSN(COMP, E, ZERO);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, left.unumber, ZERO, C_S);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(TEST, op.dest.unumber, op.dest.unumber);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, op.dest.unumber, ZERO, C_S);
				writeImmediateInsn(AND, op.dest.unumber, num - 1);
				program[writeIndex++] = INSN(COMP, left.unumber, ZERO);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, op.dest.unumber, ZERO, C_S);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, op.dest.unumber);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, op.dest.unumber, ZERO, C_S);
				writeImmediateInsn(AND, op.dest.unumber, num - 1);
				program[writeIndex++] = INSN(COMP, E, ZERO);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, op.dest.unumber, ZERO, C_S);
			}
			else if (left.unumber < 4) {
				program[writeIndex++] = INSN(SET_REG_TO_REG, E, left.unumber);
				program[writeIndex++] = INSN(TEST, left.unumber, left.unumber);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, E, ZERO, C_S);
				writeImmediateInsn(AND, E, num - 1);
				program[writeIndex++] = INSN(TEST, left.unumber, left.unumber);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, E, ZERO, C_S);
				writeFrameRegisterFromE(op.dest.unumber);
			}
			else {
				auto save = findSaveRegister(function, index);
				saveRegister(save);

				readFrameRegisterToE(left.unumber);
				program[writeIndex++] = INSN(SET_REG_TO_E, save.reg, A);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, E, ZERO, C_S);
				writeImmediateInsn(AND, E, num - 1);
				program[writeIndex++] = INSN(TEST, save.reg, save.reg);
				program[writeIndex++] = COND_INSN(SUB_REVERSE, E, ZERO, C_S);
				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save);
			}
		}
		else {
			if (left.unumber == op.dest.unumber && left.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left.unumber);

				outputConstantMod(E, save1.reg, save2.reg, left.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else if (op.dest.unumber < 4 && left.unumber < 4) {
				auto save = findSaveRegister(function, index);
				saveRegister(save, left.unumber);
				program[writeIndex++] = INSN(SET_REG_TO_REG, op.dest.unumber, left.unumber);

				outputConstantMod(E, op.dest.unumber, save.reg, left.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save);
			}
			else if (op.dest.unumber < 4) {
				readFrameRegisterToArg1(op.dest.unumber, left.unumber);
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, op.dest.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, op.dest.unumber);

				outputConstantMod(E, save1.reg, save2.reg, op.dest.unumber, right.number);

				program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else if (left.unumber < 4) {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, left.unumber);

				outputConstantMod(E, save1.reg, save2.reg, left.unumber, right.number);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1);
				readFrameRegisterToArg1(save1.reg, left.unumber);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, save1.reg);
				auto save3 = findSaveRegister(function, index, (1 << save1.reg) | (1 << save2.reg));
				saveRegister(save3, save1.reg);

				outputConstantMod(E, save2.reg, save3.reg, save1.reg, right.number);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save3);
				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else if (left.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (left.unumber < 4) {
				if (left.unumber == op.dest.unumber) {
					auto save = findSaveRegister(function, index);
					saveRegister(save, right);

					outputMod(E, left.unumber, save.reg);
					program[writeIndex++] = INSN(SET_REG_TO_E, op.dest.unumber, A);

					restoreRegister(save);
				}
				else {
					auto save = findSaveRegister(function, index);
					saveRegister(save, right);

					outputMod(op.dest.unumber, left.unumber, save.reg);

					restoreRegister(save);
				}
			}
			else { // left.unumber >= 4
				auto save = findSaveRegister(function, index);
				saveRegister(save, right);

				readFrameRegisterToE(left.unumber);

				outputMod(op.dest.unumber, E, save.reg);

				restoreRegister(save);
			}
		}
		else {
			if (left.unumber < 4) {
				auto save = findSaveRegister(function, index);
				saveRegister(save, right);

				outputMod(E, left.unumber, save.reg);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1);
				auto save2 = findSaveRegister(function, index, 1 << save1.reg);
				saveRegister(save2, right);

				readFrameRegisterToArg1(save1.reg, left.unumber);

				outputMod(E, save1.reg, save2.reg);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else if (left.type == RegType::IMMEDIATE && right.type == RegType::REGISTER) {
		if (op.dest.unumber < 4) {
			if (right.unumber < 4) {
				if (right.unumber == op.dest.unumber) {
					auto save = findSaveRegister(function, index);
					saveRegister(save, right.unumber);

					writeSubstInsn(SET_REG_TO_REG, E, left);

					outputMod(op.dest.unumber, E, save.reg);

					restoreRegister(save);
				}
				else {
					writeSubstInsn(SET_REG_TO_REG, E, left);

					program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

					outputMod(op.dest.unumber, E, right.unumber);

					program[writeIndex++] = INSN(POP, right.unumber, A);
				}
			}
			else {
				writeSubstInsn(SET_REG_TO_REG, E, left);

				auto save = findSaveRegister(function, index);

				readFrameRegisterToArg1(save.reg, right.unumber);

				outputMod(op.dest.unumber, E, save.reg);

				restoreRegister(save);
			}
		}
		else {
			if (right.unumber < 4) {
				auto save = findSaveRegister(function, index);
				saveRegister(save, left);

				program[writeIndex++] = INSN(PUSH_ARG1, right.unumber, A);

				outputMod(E, save.reg, right.unumber);

				program[writeIndex++] = INSN(POP, right.unumber, A);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save);
			}
			else {
				auto save1 = findSaveRegister(function, index);
				saveRegister(save1, left);
				auto save2 = findSaveRegister(function, index, save1.reg);

				readFrameRegisterToArg1(save2.reg, right.unumber);

				outputMod(E, save1.reg, save2.reg);

				writeFrameRegisterFromE(op.dest.unumber);

				restoreRegister(save2);
				restoreRegister(save1);
			}
		}
	}
	else {
		if (op.dest.unumber < 4) {
			writeSubstInsn(SET_REG_TO_REG, E, left);

			auto save = findSaveRegister(function, index);
			saveRegister(save, right);


			outputMod(op.dest.unumber, E, save.reg);

			restoreRegister(save);
		}
		else {
			auto save1 = findSaveRegister(function, index);
			saveRegister(save1, left);
			auto save2 = findSaveRegister(function, index, 1 << save1.reg);
			saveRegister(save2, right);

			outputMod(E, save1.reg, save2.reg);

			writeFrameRegisterFromE(op.dest.unumber);

			restoreRegister(save2);
			restoreRegister(save1);
		}
	}
}


static void writeOp(DeclFunction *function, u32 index) {
	Ir &op = function->ops[index];
	PROFILE_FUNC_DATA(irTypeNames[static_cast<u8>(op.type)]);

	switch (op.type) {
		case IrType::NOOP:
			break;
		case IrType::GOTO:
			writeGoto(function, op, C_UN);
			break;
		case IrType::IF_Z:
			writeIfZOrNz(function, index, op, C_Z);
			break;
		case IrType::IF_NZ:
			writeIfZOrNz(function, index, op, C_NZ);
			break;
		case IrType::IF_EQ:
			writeIf(function, index, op, C_Z);
			break;
		case IrType::IF_NEQ:
			writeIf(function, index, op, C_NZ);
			break;
		case IrType::IF_G:
			writeIf(function, index, op, C_G);
			break;
		case IrType::IF_LE:
			writeIf(function, index, op, C_LE);
			break;
		case IrType::IF_L:
			writeIf(function, index, op, C_L);
			break;
		case IrType::IF_GE:
			writeIf(function, index, op, C_GE);
			break;
		case IrType::IF_A:
			writeIf(function, index, op, C_A);
			break;
		case IrType::IF_BE:
			writeIf(function, index, op, C_BE);
			break;
		case IrType::IF_B:
			writeIf(function, index, op, C_B);
			break;
		case IrType::IF_AE:
			writeIf(function, index, op, C_AE);
			break;
		case IrType::IF_AND_Z:
			writeTest(function, index, op, C_Z);
			break;
		case IrType::IF_AND_NZ:
			writeTest(function, index, op, C_NZ);
			break;
		case IrType::AND:
			writeCommutativeBinary(function, index, op, AND);
			break;
		case IrType::OR:
			writeCommutativeBinary(function, index, op, OR);
			break;
		case IrType::XOR:
			writeCommutativeBinary(function, index, op, XOR);
			break;
		case IrType::ADD:
			writeCommutativeBinary(function, index, op, ADD);
			break;
		case IrType::EQ:
			writeCommutativeBinary(function, index, op, SET_EQ);
			break;
		case IrType::NOT_EQ:
			writeCommutativeBinary(function, index, op, SET_NEQ);
			break;
		case IrType::NEG:
			writeUnary(function, index, op, SUB_REVERSE, ZERO);
			break;
		case IrType::NOT:
			writeUnary(function, index, op, XOR, MINUS_ONE);
			break;
		case IrType::GREATER:
			writeCompare(function, index, op, C_G);
			break;
		case IrType::LESS_EQUAL:
			writeCompare(function, index, op, C_LE);
			break;
		case IrType::LESS:
			writeCompare(function, index, op, C_L);
			break;
		case IrType::GREATER_EQUAL:
			writeCompare(function, index, op, C_GE);
			break;
		case IrType::ABOVE:
			writeCompare(function, index, op, C_A);
			break;
		case IrType::BELOW_EQUAL:
			writeCompare(function, index, op, C_BE);
			break;
		case IrType::BELOW:
			writeCompare(function, index, op, C_B);
			break;
		case IrType::ABOVE_EQUAL:
			writeCompare(function, index, op, C_AE);
			break;
		case IrType::SET:
			writeSet(op);
			break;
		case IrType::RETURN:
			writeReturn(op);
			break;
		case IrType::READ:
			writeRead(function, index, op);
break;
		case IrType::WRITE:
			writeWrite(function, index, op);
			break;
		case IrType::LSHIFT:
			writeShift(function, index, op, SHIFT_LEFT);
			break;
		case IrType::ARSHIFT:
			writeShift(function, index, op, SHIFT_RIGHT_SIGNED);
			break;
		case IrType::RSHIFT:
			writeShift(function, index, op, SHIFT_RIGHT);
			break;
		case IrType::ARRAY:
			writeArray(op);
			break;
		case IrType::CALL:
			writeCall(function, index, op);

			if (index + 1 < function->ops.size()) {
				Ir &next = function->ops[index + 1];

				if (next.type != IrType::CALL || (next.flags & IR_IS_LEADER)) {
					writeFunctionPostamble();
				}
			}

			break;
		case IrType::SUB:
			writeSub(function, index, op);
			break;
		case IrType::MUL:
			writeMul(function, index, op);
			break;
		case IrType::DIV:
			writeDiv(function, index, op);
			break;
		case IrType::MOD:
			writeMod(function, index, op);
			break;
		default:
			assert(false);
	}
}

static void writeFunction(DeclFunction *function) {
	PROFILE_FUNC();
	doSubstitutions(function, writeIndex);

	irOpAddresses.clear();
	while (irOpSubstitutions.size() < function->ops.size()) irOpSubstitutions.add();

	u64 requiredSize = getRequiredLiveRangeInfoSize(function);

	if (liveRangeInfoSize < requiredSize) {
		liveRangeInfo = static_cast<u64 *>(realloc(liveRangeInfo, requiredSize * sizeof(u64)));
	}

	calculateLiveRanges(function, liveRangeInfo);

	useFrame = !optimizationSettings.optimizeFramePointers || function->largestReg >= 4;
	frameOffset = optimizationSettings.optimizeFramePointers && function->largestReg >= 6 ? 1 : 0;

	if (!useFrame) {
		for (const Ir &op : function->ops) {
			useFrame |= op.type == IrType::ARRAY; // If we have array statements we need to use a frame pointer
		}
	}

	if (useFrame) {
		program[writeIndex++] = INSN(PUSH_ARG1, FP, A);

		if (frameOffset) {
			writeImmediateInsn(ADD, SP, frameOffset);
			program[writeIndex++] = INSN(SET_REG_TO_SP, FP, A);

			writeImmediateInsn(ADD, SP, function->largestReg - 3 - frameOffset);
		}
		else {
			program[writeIndex++] = INSN(SET_REG_TO_SP, FP, A);

			if (function->largestReg >= 4) {
				writeImmediateInsn(ADD, SP, function->largestReg - 3);
			}
		}
	}

	if (function->shuffle) {
		for (ulang i = 0; i < function->shuffleCount; i++) {
			if (function->shuffle[i] == i) {
				function->shuffle[i] = 0xFFFF;
			}
			else if (function->shuffle[i] >= function->shuffleCount) {
				if (function->shuffle[i] < 4) {
					if (i < 4) {
						program[writeIndex++] = INSN(SET_REG_TO_REG, function->shuffle[i], i);
					}
					else {
						readFrameRegisterToArg1(function->shuffle[i], i);
					}
				}
				else {
					if (i < 4) {
						writeFrameRegisterFromArg1(i, function->shuffle[i]);
					}
					else {
						readFrameRegisterToE(i);
						writeFrameRegisterFromE(function->shuffle[i]);
					}
				}

				function->shuffle[i] = 0xFFFF;
			}
		}

		while (shuffleNotDone(function->shuffle, function->shuffleCount)) {
			for (ulang i = 0; i < function->shuffleCount; i++) {
				if (function->shuffle[i] != 0xFFFF) {
					if (function->shuffle[function->shuffle[i]] != 0xFFFF) {
						if (function->shuffle[i] < 4) {
							if (i < 4) {
								program[writeIndex++] = INSN(SWAP_REG, function->shuffle[i], i);
							}
							else {
								writeImmediateInsn(SWAP_STACK, function->shuffle[i], getFrameRegister(i));
							}
						}
						else {
							if (i < 4) {
								writeImmediateInsn(SWAP_STACK, i, getFrameRegister(function->shuffle[i]));
							}
							else {
								readFrameRegisterToE(i);
								writeImmediateInsn(SWAP_STACK, E, getFrameRegister(function->shuffle[i]));
								writeFrameRegisterFromE(i);
							}
						}


						ulang a = function->shuffle[i];
						ulang b = function->shuffle[a];

						function->shuffle[a] = 0xFFFF;
						function->shuffle[i] = i == b ? 0xFFFF : b;

					}
					else {
						if (function->shuffle[i] < 4) {
							if (i < 4) {
								program[writeIndex++] = INSN(SET_REG_TO_REG, function->shuffle[i], i);
							}
							else {
								readFrameRegisterToArg1(function->shuffle[i], i);
							}
						}
						else {
							if (i < 4) {
								writeFrameRegisterFromArg1(i, function->shuffle[i]);
							}
							else {
								readFrameRegisterToE(i);
								writeFrameRegisterFromE(function->shuffle[i]);
							}
						}

						function->shuffle[i] = 0xFFFF;
					}
				}
			}
		}

		delete[] function->shuffle;
	}

	for (u32 i = 0; i < function->ops.size(); i++) {
		Array<ulang> &substs = irOpSubstitutions[i];
		irOpAddresses.add(writeIndex);

		for (const ulang subst : substs) {
			program[subst] = irOpAddresses[i];
		}

		writeOp(function, i);
		substs.clear();
	}

	function->ops.free();
}

static void writeDeclaration(Decl *declaration) {
	PROFILE_FUNC();
	if (declaration->name == binaryEndName) {
		if (declaration->flags & DECL_IS_EXTERN) {
			if (declaration->type != DeclType::CONST) {
				reportError(declaration, "_binaryEnd is a compiler defined extern constant, it cannot be overriden.");
				if (doColorPrint) {
					reportError(declaration, "Did you mean: \x1b[93mconst extern _binaryEndDecl;\x1b[0m", "  ...");
				}
				else {
					reportError(declaration, "Did you mean: const extern _binaryEndDecl;", "  ...");
				}

				return;
			}
			else {
				binaryEndDecl.add(static_cast<DeclVar *>(declaration));
				return;
			}
		}
		else {
			reportError(declaration, "_binaryEnd is a compiler defined extern constant, it cannot be overriden.");
			if (doColorPrint) {
				reportError(declaration, "Did you mean: \x1b[93mconst extern _binaryEndDecl;\x1b[0m", "  ...");
			}
			else {
				reportError(declaration, "Did you mean: const extern _binaryEndDecl;", "  ...");
			}
			return;
		}
	}

	if (declaration->name == volatileName) {
		if (declaration->flags & DECL_IS_EXTERN) {
			if (declaration->type != DeclType::FUNCTION) {
				reportError(declaration, "_volatile is a compiler defined extern function, it cannot be overriden.");
				if (doColorPrint) {
					reportError(declaration, "Did you mean: \x1b[93mfunction extern _volatile(val);\x1b[0m", "  ...");
				}
				else {
					reportError(declaration, "Did you mean: function extern _volatile(val);", "  ...");
				}

				return;
			}
			else {
				return;
			}
		}
		else {
			reportError(declaration, "_volatile is a compiler defined extern array, it cannot be overriden.");
			if (doColorPrint) {
				reportError(declaration, "Did you mean: \x1b[93mfunction extern _volatile(val);\x1b[0m", "  ...");
			}
			else {
				reportError(declaration, "Did you mean: function extern _volatile(val);", "  ...");
			}
			return;
		}
	}

	if (declaration->name == mainName) {
		if (declaration->type != DeclType::FUNCTION) {
			reportError(declaration, "Main must be a function");
			return;
		}
		else if (declaration->flags & DECL_IS_EXTERN) {
			reportError("Main cannot be declared as extern");
			return;
		}
		else if (mainFunc) {
			reportError(declaration, msg("Cannot have multiple Main functions, one is already defined at " << mainFunc->startLocation));
			return;
		}

		mainFunc = static_cast<DeclFunction *>(declaration);
	}

	if (declaration->name == initName) {
		if (declaration->type != DeclType::FUNCTION) {
			reportError(declaration, "_Init must be a function");
			return;
		}
		else if (declaration->flags & DECL_IS_EXTERN) {
			reportError(declaration, "An _Init function cannot be declared extern");
			return;
		}

		initializers.add(static_cast<DeclFunction *>(declaration));
	}

	if (declaration->flags & DECL_IS_EXTERN) {
		reportError(declaration, msg("Unknown extern: " << declaration->name));
		return;
	}

	assert(!(declaration->flags & DECL_HAS_BEEN_WRITTEN_TO_BINARY));


	switch (declaration->type) {
		case DeclType::ARRAY:
			writeArray(static_cast<DeclArray *>(declaration));
			break;
		case DeclType::VAR:
			writeVar(static_cast<DeclVar *>(declaration));
			break;
		case DeclType::FUNCTION:
			writeFunction(static_cast<DeclFunction *>(declaration));
			break;
		case DeclType::STRING:
			writeString(static_cast<DeclString *>(declaration));
			break;
		default:
			assert(false);
	}

	PROFILE_ZONE("Write Blocks");
	for (u32 i = 0; i < writeIndex / BLOCK_SIZE; i++) {
		if (!blockWritten[i] && substsRemainingInBlock[i] == 0) {
			blockWriterQueue.add({ program + i * BLOCK_SIZE, i * BLOCK_SIZE, BLOCK_SIZE });
			blockWritten[i] = true;
		}
	}
}

static void printConstraints(Reg &reg, Constraints *constraints) {
	switch (reg.type) {
		case RegType::REGISTER:
			if (constraints[reg.unumber].size()) {

				if (constraints[reg.unumber][0].min != 0 || constraints[reg.unumber][0].max != ULANG_MAX) {

					irOutput << " <";

					for (u32 i = 0; i < constraints[reg.unumber].size(); i++) {
						Constraint &c = constraints[reg.unumber][i];

						irOutput << '[' << c.min << ", " << c.max << (i + 1 == constraints[reg.unumber].size() ? "]>" : "] U ");
					}
				}
			}
			break;
	}
}

void runCodeGen() {
	PROFILE_FUNC();
	u32 completedCount = 0;
	Constraints *constraints = nullptr;
	u64 constraintsSize = 0;

	writePreamble();

	while (true) {
		Decl *declaration = codeGenQueue.take();

		if (!declaration) {
			if (++completedCount == NUM_OPTIMIZER_THREADS + 1) { // We need to wait for each optimizer thread to complete and the resolver thread
				break;
			}
			else {
				continue;
			}
		}


		if (outputIr) {

			if (!(declaration->flags & DECL_IS_EXTERN) && declaration->type == DeclType::FUNCTION) {
				if (declaration->flags & DECL_IS_LOCAL) {
					irOutput << getFilename(declaration->startLocation.fileUid) << '$';
				}

				irOutput << declaration->name << std::endl;

				DeclFunction *function = static_cast<DeclFunction *>(declaration);

				if (optimizationSettings.useConstraints) {
					if (constraintsSize < (function->largestReg + 1ULL) * function->ops.size()) {
						u64 newSize = my_max(constraintsSize * 2ULL,
							(function->largestReg + 1ULL) * function->ops.size());

						constraints = static_cast<decltype(constraints)>(realloc(constraints, sizeof(constraints[0]) * newSize));

						for (u64 i = constraintsSize; i < newSize; i++) {
							new (constraints + i) Constraints;
						}
					}

					calculateConstraints(function, constraints);
				}

				calculateLeaders(function);

				for (u32 i = 0; i < function->ops.size(); i++) {
					Ir &op = function->ops[i];

					if (op.flags & IR_IS_LEADER)
						irOutput << std::endl;

					irOutput << i << ": " << irTypeNames[static_cast<u8>(op.type)];

					if (op.dest) {
						printReg(op.dest);
						irOutput << " <-";
					}

					for (u32 j = 0; j < op.regCount; j++) {
						if (op.type == IrType::CALL) {
							printReg(op.callRegs[j]);

							if (optimizationSettings.useConstraints)
								printConstraints(op.callRegs[j], constraints + i * (function->largestReg + 1ULL));
						}
						else {
							printReg(op.regs[j]);
							if (optimizationSettings.useConstraints)
								printConstraints(op.regs[j], constraints + i * (function->largestReg + 1ULL));
						}
					}

					switch (op.type) {
						case IrType::IF_Z:
						case IrType::IF_NZ:
						case IrType::IF_EQ:
						case IrType::IF_NEQ:
						case IrType::IF_G:
						case IrType::IF_LE:
						case IrType::IF_L:
						case IrType::IF_GE:
						case IrType::IF_A:
						case IrType::IF_BE:
						case IrType::IF_B:
						case IrType::IF_AE:
							irOutput << " GOTO " << op.jumpTarget;
							break;
						case IrType::GOTO:
							irOutput << ' ' << op.jumpTarget;
							break;
					}

					irOutput << std::endl;
				}
				irOutput << std::endl;
			}
		}


		writeDeclaration(declaration);
	}

	if (!hadErrors) {
		writePostamble();

		PROFILE_ZONE("Finish Output");
		/*FILE *file = fopen(output, "wb");

		fwrite(program, sizeof(ulang), writeIndex, file);
		fclose(file);*/

		for (u32 i = 0; i < writeIndex / BLOCK_SIZE; i++) {
			assert(substsRemainingInBlock[i] == 0);

			if (!blockWritten[i]) {
				blockWriterQueue.add({ program + i * BLOCK_SIZE, i * BLOCK_SIZE, BLOCK_SIZE });
			}
		}

		u32 remaining = writeIndex % BLOCK_SIZE;

		if (remaining) {
			assert(substsRemainingInBlock[writeIndex / BLOCK_SIZE] == 0);
			u32 start = writeIndex - remaining;

			blockWriterQueue.add({ program + start, start, remaining });
		}
		
		std::cout << writeIndex << " words written" << std::endl;
	}

	blockWriterQueue.add({ nullptr, 0 });
}


void resetCodeGen() {
	writeIndex = 0;

	mainFunc = nullptr;
	initializers.clear();
	binaryEndDecl.clear();


	memset(blockWritten, 0, sizeof(blockWritten));
	memset(substsRemainingInBlock, 0, sizeof(substsRemainingInBlock));
}