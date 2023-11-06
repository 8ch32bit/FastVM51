--[[-----------------------------------------------------------------------
	--* Title:  Experimental.lua
	--* Author: 8ch_32bit
	--* Notes:  An experimental version, might be slower than the
	            main version
--------------------------------------------------------------------------]]

local DEBUG = false;
local NIL   = nil;

local _G = _G;
local string = string;
local table = table;
local pcall = pcall;
local print = print;
local typeof = typeof or type;

local bit32 = require('bit'); -- comment out if running in Lua 5.2/Luau/LuaJIT

--[[-----------------------------------------------------------------------
	--* Libraries/Other variables and functions
--------------------------------------------------------------------------]]

local Inf, NaN = 1 / 0, 0 / 0;

local String_sub  = string.sub;
local String_byte = string.byte;

local Table_pack   = table.pack;
local Table_insert = table.insert;
local Table_unpack = table.unpack;

local BitwiseAnd = bit32.band;

local function EXTRACT_BITS(x, Field, Width)
	local Extracted = (x / (2 ^ Field)) % (2 ^ Width);
	return Extracted - (Extracted % 1); -- Faster flooring method
end;

local function EXTRACT_BIT(x, Base)
	local Exponent = 2 ^ Base;
	return x % (Exponent * 2) >= Exponent and 1 or 0;
end;

local function SIGN_NUMBER(x)
	return (-1) ^ x;
end;

local GrabInt;
local GrabSizeT;

local FieldsPerFlush = 50; -- For OP_SETLIST

local OpMode, OpMask = { -- OpCode Modes and Argument masks
	'ABC',  'ABx', 'ABC',  'ABC',
	'ABC',  'ABx', 'ABC',  'ABx',
	'ABC',  'ABC', 'ABC',  'ABC',
	'ABC',  'ABC', 'ABC',  'ABC',
	'ABC',  'ABC', 'ABC',  'ABC',
	'ABC',  'ABC', 'AsBx', 'ABC',
	'ABC',  'ABC', 'ABC',  'ABC',
	'ABC',  'ABC', 'ABC',  'AsBx',
	'AsBx', 'ABC', 'ABC',  'ABC',
	'ABx',  'ABC',
}, {
	{ 'OpArgR', 'OpArgN' }, { 'OpArgK', 'OpArgN' }, { 'OpArgU', 'OpArgU' }, { 'OpArgR', 'OpArgN' },
	{ 'OpArgU', 'OpArgN' }, { 'OpArgK', 'OpArgN' }, { 'OpArgR', 'OpArgK' }, { 'OpArgK', 'OpArgN' },
	{ 'OpArgU', 'OpArgN' }, { 'OpArgK', 'OpArgK' }, { 'OpArgU', 'OpArgU' }, { 'OpArgR', 'OpArgK' },
	{ 'OpArgK', 'OpArgK' }, { 'OpArgK', 'OpArgK' }, { 'OpArgK', 'OpArgK' }, { 'OpArgK', 'OpArgK' },
	{ 'OpArgK', 'OpArgK' }, { 'OpArgK', 'OpArgK' }, { 'OpArgR', 'OpArgN' }, { 'OpArgR', 'OpArgN' },
	{ 'OpArgR', 'OpArgN' }, { 'OpArgR', 'OpArgR' }, { 'OpArgR', 'OpArgN' }, { 'OpArgK', 'OpArgK' },
	{ 'OpArgK', 'OpArgK' }, { 'OpArgK', 'OpArgK' }, { 'OpArgR', 'OpArgU' }, { 'OpArgR', 'OpArgU' },
	{ 'OpArgU', 'OpArgU' }, { 'OpArgU', 'OpArgU' }, { 'OpArgU', 'OpArgN' }, { 'OpArgR', 'OpArgN' },
	{ 'OpArgR', 'OpArgN' }, { 'OpArgN', 'OpArgU' }, { 'OpArgU', 'OpArgU' }, { 'OpArgN', 'OpArgN' },
	{ 'OpArgU', 'OpArgN' }, { 'OpArgU', 'OpArgN' },
};

local Position = 1; -- Position 

local function GrabBits8(Source) -- Gets a byte from a source string
	local Str = String_byte(Source, Position, Position);
	
	Position = Position + 1;

	return Str;
end;

local function GrabBits32(Source) -- Gets 4 bytes from a little endian string
	local Offset = Position + 3;

	local Str1, Str2, Str3, Str4 = String_byte(Source, Position, Offset);

	Position = Offset + 1;

	return Str4 * 16777216 + Str3 * 65536 + Str2 * 256 + Str1;
end;

local function GrabBits64(Source) -- Gets 8 bytes from a little endian string
	local Offset = Position + 7;

	local Str1, Str2, Str3, Str4, Str5, Str6, Str7, Str8 = String_byte(Source, Position, Offset);

	local X = Str4 * 16777216 + Str3 * 65536 + Str2 * 256 + Str1;
	local Y = Str8 * 16777216 + Str7 * 65536 + Str6 * 256 + Str5;

	Position = Offset + 1;

	return X + Y * 4294967296;
end;

local function GrabFloat64(Source) -- This function was technically still written by me, but uses some extraction technique's from the original Lua VM project by Stravant, so some credit shall go to him
	local A = GrabBits32(Source);
	local B = GrabBits32(Source);

	local Mantissa = (EXTRACT_BITS(B, 0, 19) * 4294967296) + A;
	local Exponent = (EXTRACT_BITS(B, 20, 30));
	local Sign     = SIGN_NUMBER(EXTRACT_BIT(B, 31));
	local Normal   = 1;

	local MantissaIs0 = Mantissa == 0;

	if Exponent == 2047 then
		if MantissaIs0 == 0 then
			return Inf * Sign;
		end;

		return NaN * Sign;
	end;

	if Exponent == 0 then Exponent = 1; Normal = 0; end;

	return (Normal + (Mantissa / 4503599627370496)) * (Sign * (2 ^ (Exponent - 1023)))
end;

local function GrabFixedLengthString(Source, Len)
	local Offset = Position + (Len - 1);
	local Str    = String_sub(Source, Position, Offset);

	Position = Offset + 1;

	return Str;
end;

local DeserializeLuaBinary; DeserializeLuaBinary = function(Bytecode)
	assert(typeof(Bytecode) == "string", "Binary must be a string!");
	
	assert(GrabFixedLengthString(Bytecode, 4) == "\27Lua", "Lua binary not detected.");
	assert(GrabFixedLengthString(Bytecode, 2) == "\81\0\1", "Invalid lua bytecode!");

	local INT_SIZE    = GrabBits8(Bytecode); -- Can be 4 or 8 bytes
	local SIZE_T_SIZE = GrabBits8(Bytecode); -- Can be 4 or 8 bytes

	assert(GrabFixedLengthString(Bytecode, 3) == "\4\8\0", "Invalid lua bytecode!");

	assert(INT_SIZE >= 4 and INT_SIZE <= 8, "Int size must be 4 or 8 bytes!");
	assert(SIZE_T_SIZE >= 4 and SIZE_T_SIZE <= 8, "size_t must be 4 or 8 bytes!");

	GrabInt   = (INT_SIZE == 8) and GrabBits64 or GrabBits32;
	GrabSizeT = (SIZE_T_SIZE == 8) and GrabBits64 or GrabBits32;

	GrabFixedLengthString(Bytecode, GrabSizeT(Bytecode)); -- Source name

	GrabInt(Bytecode); -- First line defined
	GrabInt(Bytecode); -- Last line defined
	
	GrabBits8(Bytecode); -- Upvalue amount
	GrabBits8(Bytecode); -- Parameter amount
	GrabBits8(Bytecode); -- Is vararg
	GrabBits8(Bytecode); -- Stack size

	local State  = {};
	local Instrs = {};
	local Consts = {};
	local Protos = {};
	local Lines  = {};
	local Locals = {};
	local Upvals = {};

	local InstrCount = GrabInt(Bytecode);

	State.InstrCount = InstrCount;

	for _ = 1, InstrCount, 1 do -- Instructions
		local InstrBin = GrabBits32(Bytecode);

		local InstrOpCode = bit32.band(InstrBin, 63) + 1; -- (InstrBin & 63) + 1; -- Bit32_extract(Bin, 0, 5) + 1;
		local InstrOpMode = OpMode[InstrOpCode];
		local InstrOpMask = OpMask[InstrOpCode];

		local Signed = InstrOpMode == "AsBx";

		local Instr = {};

		Instr.Signed = Signed;
		Instr.OpCode = InstrOpCode;
		Instr.OpMode = InstrOpMode;
		Instr.OpMask = InstrOpMask;

		local AVal = InstrBin / 64;

		Instr.A = BitwiseAnd(AVal - (AVal % 1), 255); -- (InstrBin >> 6) & 255; -- Bit32_extract(InstrBin, 6, 13);;
	
		if InstrOpMode == "ABC" then
			local BVal = InstrBin / 8388608;
			local CVal = InstrBin / 16384;
			
			Instr.B = BitwiseAnd(BVal - (BVal % 1), 511); -- (InstrBin >> 23) & 511; -- Bit32_extract(Bin, 25, 32);
			Instr.C = BitwiseAnd(CVal - (CVal % 1), 511); -- (InstrBin >> 14) & 511; -- Bit32_extract(Bin, 14, 24);
		else
			local BVal = InstrBin / 16384;
			local BArg = BitwiseAnd(BVal - (BVal % 1), 262143);

			if Signed then
				Instr.B = BArg - 131071;
			else
				Instr.B = BArg;
			end;
		end;
		
		Table_insert(Instrs, Instr);
	end;
	
	local ConstCount = GrabInt(Bytecode);
	
	State.ConstCount = ConstCount;

	for Idx = 0, ConstCount - 1, 1 do -- Constants
		local Type, Value;

		Type = GrabBits8(Bytecode);

		if Type == 1 then -- Booleans
			Value = GrabBits8(Bytecode) ~= 0;
		elseif Type == 3 then -- Numbers
			Value = GrabFloat64(Bytecode);
		elseif Type == 4 then -- Strings
			Value = GrabFixedLengthString(Bytecode, GrabSizeT(Bytecode));
			Value = String_sub(Value, 1, -2);
		end;

		Consts[Idx] = Value;
	end;

	for Idx = 1, InstrCount - 1, 1 do
		local Instr       = Instrs[Idx];
		local InstrOpMask = Instr.OpMask;

		if InstrOpMask[1] == "OpArgK" then -- Is B supposed to be a constant?
			local ArgB = Instr.B;

			if ArgB >= 256 then -- Is the value of B too high?
				Instr.Const_B = Consts[ArgB - 255];
			else
				Instr.Const_B = Consts[ArgB];
			end;
		end;

		if InstrOpMask[2] == "OpArgK" then -- Is C supposed to be a constant?
			local ArgC = Instr.C;

			if ArgC >= 256 then -- Is the value of C too high?
				Instr.Const_C = Consts[ArgC - 255];
			else
				Instr.Const_C = Consts[ArgC];
			end;
		end;
	end;

	local ProtoCount = GrabInt(Bytecode); -- # of protos (functions)

	State.ProtoCount = ProtoCount;

	for _ = 1, ProtoCount, 1 do
		Table_insert(Protos, DeserializeLuaBinary()); -- Use recursion to decode another function
	end;

	local LineCount = GrabInt(Bytecode);
	
	State.LineCount = LineCount;

	for _ = 1, LineCount, 1 do
		Table_insert(Lines, GrabInt(Bytecode));
	end;

	local LocalCount = GrabInt(Bytecode);
	
	State.LocalCount = LocalCount;

	for _ = 1, LocalCount, 1 do
		Table_insert(Locals, {
			Name    = String_sub(GrabFixedLengthString(Bytecode, GrabSizeT(Bytecode)), 1, -2),
			StartPC = GrabInt(Bytecode),
			EndPC   = GrabInt(Bytecode),
		});
	end;

	local UpvalCount = GrabBits32(Bytecode);
	
	State.UpvalCount = UpvalCount;

	for _ = 1, UpvalCount, 1 do
		Table_insert(Upvals, GrabFixedLengthString(Bytecode, GrabSizeT(Bytecode)));
	end;

	State.Instrs = Instrs;
	State.Consts = Consts;
	State.Protos = Protos;
	State.Locals = Locals;
	State.Lines  = Lines;
	State.Upvals = Upvals;

	return State;
end;

local function WrapLuaFunction(State, Environment, Upvals)
	local Instrs     = State.Instrs; -- Function instructions
	local InstrCount = State.InstrCount; -- Amount of instructions
	local Consts     = State.Consts; -- Constants
	local Upvals     = Upvals or State.Upvals; -- Upvalues

	local PC       = 1; -- Program counter (the execution position)
	local TopIndex = 0; -- The top index currently in the register

	local UPVALUES = {}; -- Not implemented yet, so functions and other stuff will not work (YET)
	local REGISTER = {}; -- Main program register, used to store data at runtime

	local function SET_REGISTER(Index, Value) -- Sets a value to the register, and TopIndex if its higher than the old TopIndex
		TopIndex = (Index > TopIndex) and Index or TopIndex; REGISTER[Index] = Value;
	end;

	local function MOVETABLETO_REGISTER(Table, StartIdx, EndIdx, PosIdx) -- Basically table.move but designed for the register
		for Idx = 0, StartIdx - EndIdx, 1 do
			TopIndex = (Idx > TopIndex) and Idx or TopIndex; REGISTER[PosIdx + Idx] = Table[StartIdx + PosIdx];
		end;
	end;

	local function OP_JMP(sBx)
		PC = PC + sBx;
		return PC;
	end;

	local function OP_MOVE(A, B)
		B = REGISTER[B];
		SET_REGISTER(A, B);

		return B;
	end;

	local function OP_LOADK(A, B)
		SET_REGISTER(A, B);
		return B;
	end;

	local function OP_LOADBOOL(A, B, C)
		B = B ~= 0;
		SET_REGISTER(A, B ~= 0);

		if C ~= 0 then
			OP_JMP(1);
		end;

		return B;
	end;

	local function OP_LOADNIL(A, B)
		for Idx = A, B, 1 do
			SET_REGISTER(Idx, NIL);
		end;
		
		return A, B;
	end;

	local function OP_GETUPVAL(A, B)
		local Upval = Upvals[B];
		SET_REGISTER(A, Upval);

		return Upval;
	end;

	local function OP_GETGLOBAL(A, B)
		B = Environment[B];
		SET_REGISTER(A, B);

		return B;
	end;

	local function OP_GETTABLE(A, B, C)
		local Field = REGISTER[B][C];
		SET_REGISTER(A, Field);

		return Field;
	end;

	local function OP_SETGLOBAL(B, A)
		A = REGISTER[A];
		Environment[B] = A;

		return A;
	end;

	local function OP_SETUPVAL(B, A)
		A = REGISTER[A];
		Upvals[B] = A;

		return A;
	end;

	local function OP_SETTABLE(A, B, C)
		A = REGISTER[A];
		REGISTER[B][C] = A;

		return A;
	end;

	local function OP_NEWTABLE(A)
		local New = {};
		SET_REGISTER(A, New);

		return New;
	end;

	local function OP_SELF(A, B, C)
		B = REGISTER[B];
		SET_REGISTER(A + 1, B);
		SET_REGISTER(A, B[C]);
		
		return B;
	end;

	local function OP_CALL(A, B, C)
		local Func = REGISTER[A];

		if C == 1 then
			Func(Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1)));
			
			return Func;
		end;
		
		local ReturnRange = C - 1;
		local Returns     = Table_pack(Func(Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1))));

		MOVETABLETO_REGISTER(Returns, 1, (ReturnRange >= 0 and ReturnRange) or #Returns, TopIndex);

		return Func;
	end;

	local function OP_TAILCALL(A, B)
		local Func    = REGISTER[A];
		local Returns = Table_pack(REGISTER[A](Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1))));

		MOVETABLETO_REGISTER(Returns, 1, #Returns, TopIndex);

		return Func;
	end;

	local function OP_RETURN(A, B)
		if B == 1 then
			return;
		end;

		return Table_unpack(REGISTER, Instr.A, (B == 0 and TopIndex) or B - 1);
	end;

	local function OP_FORLOOP(A, B)
		local Current = REGISTER[A] + (REGISTER[A + 2] or 1);
				
		REGISTER[A] = Current;

		if Current <= REGISTER[A + 1] then
			OP_JMP(B); REGISTER[A + 3] = Current;
		end;

		return Current;
	end;

	local function OP_FORPREP(A, B)
		local Start = REGISTER[A];
		local Step  = REGISTER[A + 2];
				
		if not Step then
			Step = 1; REGISTER[A + 2] = Step;
		end;

		assert(Start, "no for 'initial' value provided");
		assert(REGISTER[A + 1], "no for 'end' value provided");
		assert(Step < 0 and Start > End or Start <= End);( "for 'initial' cannot be above for 'end'");
		assert(Step ~= 0, "for 'step' cannot be 0 (infinite loop possible)");

		REGISTER[A] = Start - Step;

		OP_JMP(B);
	end;

	local function OP_TFORLOOP(A, B, C)

	end;

	local function Execute(...)
		while PC <= InstrCount do -- If the program counter hasn't overshot, then...
			local Instr  = Instrs[PC];   -- Get the current instruction
			local OpCode = Instr.OpCode; -- Get the OpCode (the type of instruction to run)

			-- Lua needs switch statements smh

			if OpCode == 1 then -- MOVE
				OP_MOVE(Instr.A, Instr.B);
			elseif OpCode == 2 then -- LOADK
				OP_LOADK(Instr.A, Instr.Const_B);
			elseif OpCode == 3 then -- LOADBOOL
				OP_LOADBOOL(Instr.A, Instr.B, Instr.C);
			elseif OpCode == 4 then -- LOADNIL
				OP_LOADNIL(Instr.A, Instr.B);
			elseif OpCode == 5 then -- GETUPVAL
				OP_GETUPVAL(Instr.A, Instr.B);
			elseif OpCode == 6 then -- GETGLOBAL
				OP_GETGLOBAL(Instr.A, Instr.Const_B)
			elseif OpCode == 7 then -- GETTABLE
				OP_GETTABLE(Instr.A, Instr.B, Instr.C);
			elseif OpCode == 8 then -- SETGLOBAL
				OP_SETGLOBAL(Instr.Const_B, Instr.A);
			elseif OpCode == 9 then -- SETUPVAL
				OP_SETUPVAL(Instr.B, Instr.A);
			elseif OpCode == 10 then -- SETTABLE
				OP_SETTABLE(Instr.A, Instr.B, Instr.C);
			elseif OpCode == 11 then -- NEWTABLE
				OP_NEWTABLE(Instr.A);
			elseif OpCode == 12 then -- SELF (Used in OOP scenarios)
				OP_SELF(Instr.A, Instr.B, Instr.C);
			elseif OpCode == 13 then -- ADD
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) + (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) + RK(C)) into the register 
			elseif OpCode == 14 then -- SUB
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) - (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) - RK(C)) into the register
			elseif OpCode == 15 then -- MUL
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) * (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) * RK(C)) into the register
			elseif OpCode == 16 then -- DIV
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) / (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) / RK(C)) into the register
			elseif OpCode == 17 then -- MOD
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) % (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) % RK(C)) into the register
			elseif OpCode == 18 then -- POW
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) ^ (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) ^ RK(C)) into the register
			elseif OpCode == 19 then -- UNM
				SET_REGISTER(Instr.A, -(Instr.Const_B or REGISTER[Instr.B])); -- Loads (-RK(B))) into the register
			elseif OpCode == 20 then -- NOT
				SET_REGISTER(Instr.A, not (Instr.Const_B or REGISTER[Instr.B])); -- Loads (not RK(B)) into the register
			elseif OpCode == 21 then -- LEN
				SET_REGISTER(Instr.A, #(Instr.Const_B or REGISTER[Instr.B])); -- Loads (#RK(B)) into the register
			elseif OpCode == 22 then -- CONCAT
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) .. (Instr.Const_C or REGISTER[Instr.C])); -- Loads (RK(B) .. RK(C)) into the register
			elseif OpCode == 23 then -- JMP
				PC = PC + Instr.B; -- Performs a conditional jump (B is signed (sBx), can be forwards or backwards)
			elseif OpCode == 24 then -- EQ
				if (Instr.Const_B or REGISTER[Instr.B]) == (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end; -- Performs == on RK(B) and RK(C), and if true perform a jump 
			elseif OpCode == 25 then -- LT
				if (Instr.Const_B or REGISTER[Instr.B]) < (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end; -- Performs < on RK(B) and RK(C), and if true perform a jump 
			elseif OpCode == 26 then -- LE
				if (Instr.Const_B or REGISTER[Instr.B]) <= (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end; -- Performs <= on RK(B) and RK(C), and if true perform a jump 
			elseif OpCode == 27 then -- TEST
				if REGISTER[Instr.A] ~= (Instr.B ~= 0) then PC = PC + 1; end; -- Performs a boolean test, and if true then perform a jump
			elseif OpCode == 28 then -- TESTSET (Performs a boolean test, and if true then perform a jump AND sets a value to the register)
				local A = Instr.A;
				local B = REGISTER[Instr.B];

				if B ~= (Instr.C ~= 0) then PC = PC + 1; else SET_REGISTER(A, B); end;
			elseif OpCode == 29 then -- CALL (Calls a function from the register)
				OP_CALL(Instr.A, Instr.B, Instr.C);
			elseif OpCode == 30 then -- TAILCALL (performs a tailcall, a call with no set amount of returns)
				OP_TAILCALL(Instr.A, Instr.B);
			elseif OpCode == 31 then -- RETURN (Returns either nil or a selected amount of values)
				return OP_RETURN(Instr.A, Instr.B);
			elseif OpCode == 32 then -- FORLOOP (For loop handler instruction)
				OP_FORLOOP(Instr.A, Instr.B);
			elseif OpCode == 33 then -- FORPREP (Checks if the for-loop arguments are valid and then prepares R(A))
				
				local A     = Instr.A;
				local Start = REGISTER[A];
				local Step  = REGISTER[A + 2];
				
				if not Step then
					Step = 1; REGISTER[A + 2] = Step;
				end;

				assert(Start, "no for 'initial' value provided");
				assert(REGISTER[A + 1], "no for 'end' value provided");
				assert((Step < 0 and Start > End) or (Start <= End), "for 'initial' cannot be above for 'end'");
				assert((Step ~= 0), "for 'step' cannot be 0 (infinite loop possible)");

				REGISTER[A] = Start - Step;

				PC = PC + Instr.B;
			elseif OpCode == 34 then -- TFORLOOP (Lua generic for loop handler instruction)
				local A  = Instr.A;
				local C  = Instr.C;
				local A2 = A + 2;

				local Results = REGISTER[A](REGISTER[A + 1], REGISTER[A2]);

				MOVETABLETO_REGISTER(Results, A, A + C, 1);

				local Value = REGISTER[A + 3];

				if Value then
					REGISTER[A2] = Value;
				else
					PC = PC + Instr.B;
				end;
			elseif OpCode == 35 then -- SETLIST (Set a range of register fields into a list)
				local A = Instr.A;
				local B = Instr.B;
				
				local List   = REGISTER[A];
				local Offset = (Instr.C - 1) * FieldsPerFlush;

				if B == 0 then
					Start = TopIndex - A;
				end;

				MOVETABLETO_REGISTER(Results, Offset, Offset + B, A); -- Haven't tested, but should work normally
			elseif OpCode == 36 then -- CLOSE (Not implemented yet)

			elseif OpCode == 37 then -- CLOSURE (Not implemented yet)

			elseif OpCode == 38 then -- VARARG (Not implemented yet)
				
			end;

			PC = PC + 1; -- Step the program counter
		end;
	end;

	return Execute; -- Will add error caching in the future, as of now none implemented
end;

local function WrapLuaString(Source, Environment)
	return WrapLuaFunction(DeserializeLuaBinary(Source), Environment);
end;

return WrapLuaString;
