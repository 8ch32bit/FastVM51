--[[-----------------------------------------------------------------------
	--* Title:  Main.lua
	--* Author: 8ch_32bit
	--* Notes:  THE FASTEST LUA 5.1 VM EVERRRR
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

local function dP(...)
	if DEBUG then print(...); end; return ...;
end;

--[[-----------------------------------------------------------------------
	--* Libraries/Other variables and functions
--------------------------------------------------------------------------]]

local Inf, NaN = 1 / 0, 0 / 0;

local String_sub  = string.sub;
local String_byte = string.byte;

local Table_pack   = table.pack;
local Table_insert = table.insert;
local Table_unpack = table.unpack;

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

--[[local function GrabFloat64(Source) -- My own take on float extraction (returned incorrect results, very buggy)
	local Mantissa = 0;
	local Exponent = 0;
	local Sign     = 0;
	local Normal   = 1;

	local X = GrabBits32(Source);
	local Y = GrabBits32(Source);

	--local Mantissa = X + Bit32_extract(Y, 1, 20);

	Mantissa, Exponent, Sign = X + Bit32_extract(Y, 1, 20) * 4294967296 , Bit32_extract(Y, 21, 31), (-1) ^ ExtractBit(Y, 32);

	if Mantissa == 0 and Exponent == 0 then
		return 0;
	end;

	if Mantissa == 0 and Exponent == 2047 then
		return Inf;
	end;

	if Mantissa ~= 0 and Exponent == 2047 then
		return NaN;
	end;

	local Condition = Mantissa ~= 0 and Exponent == 0;

	Exponent = (Condition and 1) or Exponent;
	Normal   = (Condition and 0) or Normal;

	return Normal + (Mantissa / 4503599627370496) * Sign * 2 ^ (Exponent - 1023);
end;]]

local function GrabFixedLengthString(Source, Len)
	local Offset = Position + (Len - 1);
	local Str    = String_sub(Source, Position, Offset);

	Position = Offset + 1;

	return Str;
end;

local DeserializeLuaBinary; DeserializeLuaBinary = function(Bytecode)
	assert(typeof(Bytecode) == "string", "Binary must be a string!");
	assert(dP(GrabFixedLengthString(Bytecode, 4)) == "\27Lua", "Unknown binary!");
	assert(dP(GrabBits8(Bytecode)) == 81, "Lua version must be 5.1!");
	assert(dP(GrabBits8(Bytecode)) == 0, "Must be official lua format!");
	assert(dP(GrabBits8(Bytecode)) == 1, "Must be a little endian bytecode!");

	local INT_SIZE    = dP(GrabBits8(Bytecode));
	local SIZE_T_SIZE = dP(GrabBits8(Bytecode));

	assert(INT_SIZE >= 4 and INT_SIZE <= 8, "Int size must be 4 or 8 bytes!");
	assert(SIZE_T_SIZE >= 4 and SIZE_T_SIZE <= 8, "size_t must be 4 or 8 bytes!");

	GrabInt   = (INT_SIZE == 8) and GrabBits64 or GrabBits32;
	GrabSizeT = (SIZE_T_SIZE == 8) and GrabBits64 or GrabBits32;

	assert(dP(GrabBits8(Bytecode)) == 4, "Instruction size must be 4 bytes!");
	assert(dP(GrabBits8(Bytecode)) == 8, "Num size must be 8 bytes!");
	assert(dP(GrabBits8(Bytecode)) == 0, "Numbers must be floating point!");

	dP(GrabFixedLengthString(Bytecode, GrabBits32(Bytecode))); -- Source name

	dP(GrabInt(Bytecode)); -- First line defined
	dP(GrabInt(Bytecode)); -- Last line defined
	
	dP(GrabBits8(Bytecode)); -- Upvalue amount
	dP(GrabBits8(Bytecode)); -- Parameter amount
	dP(GrabBits8(Bytecode)); -- Is vararg
	dP(GrabBits8(Bytecode)); -- Stack size

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

		local Instr = {};

		Instr.Signed = InstrOpMode == "AsBx";
		Instr.OpCode = InstrOpCode;
		Instr.OpMode = InstrOpMode;
		Instr.OpMask = InstrOpMask;

		local ArgAValue = InstrBin / 64;
		ArgAValue = ArgAValue - (ArgAValue % 1); -- Remove decimal points

		Instr.A = bit32.band(ArgAValue, 255); -- (InstrBin >> 6) & 255; -- Bit32_extract(InstrBin, 6, 13);;
	
		if InstrOpMode == "ABC" then
			Instr.B = bit32.band(bit32.rshift(InstrBin, 23), 511); -- (InstrBin >> 23) & 511; -- Bit32_extract(Bin, 25, 32);
			Instr.C = bit32.band(bit32.rshift(InstrBin, 14), 511); -- (InstrBin >> 14) & 511; -- Bit32_extract(Bin, 14, 24);
		elseif InstrOpMode == "ABx" then
			Instr.B = bit32.band(bit32.rshift(InstrBin, 14), 262143); -- (InstrBin >> 14) & 262143; -- Bit32_extract(Bin, 14, 32);
		else
			Instr.B = bit32.band(bit32.rshift(InstrBin, 14), 262143) - 131071; -- (InstrBin >> 14) & 262143 - 131071; -- Bit32_extract(Bin, 14, 32) - 131071;
		end;
		
		Table_insert(Instrs, Instr);
	end;
	
	local ConstCount = GrabInt(Bytecode);
	
	State.ConstCount = ConstCount;

	for Idx = 0, ConstCount - 1, 1 do -- Constants
		local Type, Value;

		Type = GrabBits8(Bytecode);

		if Type == 1 then -- Lua needs switch statements
			Value = GrabBits8(Bytecode) ~= 0;
		elseif Type == 3 then
			Value = GrabFloat64(Bytecode);
		elseif Type == 4 then
			Value = GrabFixedLengthString(Bytecode, GrabSizeT(Bytecode));
			Value = String_sub(Value, 1, -2);
		end;

		Consts[Idx] = Value;
	end;

	for Idx = 1, InstrCount - 1, 1 do
		local Instr       = Instrs[Idx];
		local InstrOpMask = Instr.OpMask;

		if InstrOpMask[1] == "OpArgK" then
			local ArgB = Instr.B;

			if ArgB >= 256 then
				Instr.Const_B = Consts[ArgB - 255];
			else
				Instr.Const_B = Consts[ArgB];
			end;
		end;

		if InstrOpMask[2] == "OpArgK" then
			local ArgC = Instr.C;

			if ArgC >= 256 then
				Instr.Const_C = Consts[ArgC - 255];
			else
				Instr.Const_C = Consts[ArgC];
			end;
		end;
	end;

	local ProtoCount = GrabInt(Bytecode);

	State.ProtoCount = ProtoCount;

	for _ = 1, ProtoCount, 1 do
		Table_insert(Protos, DeserializeLuaBinary());
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
	local Instrs     = State.Instrs;
	local InstrCount = State.InstrCount;
	local Consts     = State.Consts;
	local Upvals     = Upvals or State.Upvals;

	local PC       = 1; -- Program counter (the execution position)
	local TopIndex = 0; -- The top index currently in the register

	local UPVALUES = {}; -- Not implemented yet, so functions and other stuff will not work (YET)
	local REGISTER = {}; 

	local function SET_REGISTER(Index, Value)
		TopIndex = (Index > TopIndex) and Index or TopIndex; REGISTER[Index] = Value;
	end;

	local function MOVETABLETO_REGISTER(Table, StartIdx, EndIdx, PosIdx) -- Basically table.move but designed for REGISTER
		for Idx = 0, StartIdx - EndIdx, 1 do
			TopIndex = (Idx > TopIndex) and Idx or TopIndex; REGISTER[PosIdx + Idx] = Table[StartIdx + PosIdx];
		end;
	end;

	local function Execute(...)
		while PC <= InstrCount do
			local Instr  = Instrs[PC];
			local OpCode = Instr.OpCode;

			-- Lua needs switch statements smh (!!messy if statement warning!!)

			if OpCode == 1 then -- MOVE
				SET_REGISTER(Instr.A, REGISTER[Instr.B]);
			elseif OpCode == 2 then -- LOADK
				SET_REGISTER(Instr.A, Instr.Const_B or Consts[Instr.B]);
			elseif OpCode == 3 then -- LOADBOOL
				SET_REGISTER(Instr.A, Instr.B ~= 0);

				if (Instr.C ~= 0) then PC = PC + 1; end;
			elseif OpCode == 4 then -- LOADNIL
				for Idx = Instr.A, Instr.B, 1 do SET_REGISTER(Idx, NIL); end;
			elseif OpCode == 5 then -- GETUPVAL
				SET_REGISTER(Instr.A, Upvals[Instr.B]);
			elseif OpCode == 6 then -- GETGLOBAL
				SET_REGISTER(Instr.A, Environment[Instr.Const_B]);
			elseif OpCode == 7 then -- GETTABLE
				SET_REGISTER(Instr.A, REGISTER[Instr.B][Instr.C]);
			elseif OpCode == 8 then -- SETGLOBAL
				Environment[Instr.Const_B or Instr.B] = Consts[Instr.A];
			elseif OpCode == 9 then -- SETUPVAL
				Upvals[Instr.A] = REGISTER[Instr.B]; -- might be inverse, left this here for future notice
			elseif OpCode == 10 then -- SETTABLE
				REGISTER[Instr.A][Instr.B] = REGISTER[Instr.C];
			elseif OpCode == 11 then -- NEWTABLE
				SET_REGISTER(Instr.A, {});
			elseif OpCode == 12 then -- SELF
				local A = Instr.A;
				local B = REGISTER[Instr.B];

				SET_REGISTER(A + 1, B);
				SET_REGISTER(A, B[Instr.C]);
			elseif OpCode == 13 then -- ADD
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) + (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 14 then -- SUB
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) - (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 15 then -- MUL
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) * (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 16 then -- DIV
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) / (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 17 then -- MOD
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) % (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 18 then -- POW
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) ^ (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 19 then -- UNM
				SET_REGISTER(Instr.A, -(Instr.Const_B or REGISTER[Instr.B]));
			elseif OpCode == 20 then -- NOT
				SET_REGISTER(Instr.A, not (Instr.Const_B or REGISTER[Instr.B]));
			elseif OpCode == 21 then -- LEN
				SET_REGISTER(Instr.A, #(Instr.Const_B or REGISTER[Instr.B]));
			elseif OpCode == 22 then -- CONCAT
				SET_REGISTER(Instr.A, (Instr.Const_B or REGISTER[Instr.B]) .. (Instr.Const_C or REGISTER[Instr.C]));
			elseif OpCode == 23 then -- JMP
				PC = PC + Instr.B;
			elseif OpCode == 24 then -- EQ
				if (Instr.Const_B or REGISTER[Instr.B]) == (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end;
			elseif OpCode == 25 then -- LT
				if (Instr.Const_B or REGISTER[Instr.B]) < (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end;
			elseif OpCode == 26 then -- LE
				if (Instr.Const_B or REGISTER[Instr.B]) <= (Instr.Const_C or REGISTER[Instr.C]) then PC = PC + 1; end;
			elseif OpCode == 27 then -- TEST
				if REGISTER[Instr.A] ~= (Instr.B ~= 0) then PC = PC + 1; end;
			elseif OpCode == 28 then -- TESTSET
				local A = Instr.A;
				local B = REGISTER[Instr.B];

				if B ~= (Instr.C ~= 0) then PC = PC + 1; else SET_REGISTER(A, B); end;
			elseif OpCode == 29 then -- CALL
				local A = Instr.A;
				local B = Instr.B;
				local C = Instr.C;

				if C ~= 1 then
					local ReturnRange = C - 1;
					local Returns     = Table_pack(REGISTER[A](Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1))));

					MOVETABLETO_REGISTER(Returns, 1, (ReturnRange >= 0 and ReturnRange) or #Returns, TopIndex);
				else
					REGISTER[A](Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1)));
				end;
			elseif OpCode == 30 then -- TAILCALL
				local A = Instr.A;
				local B = Instr.B;

				local Returns = Table_pack(REGISTER[A](Table_unpack(REGISTER, A + 1, A + (B == 0 and (TopIndex - A) or B - 1))));

				MOVETABLETO_REGISTER(Returns, 1, #Returns, TopIndex);
			elseif OpCode == 31 then -- RETURN
				local B = Instr.B;

				if B == 1 then return; end;

				return Table_unpack(REGISTER, Instr.A, (B == 0 and TopIndex) or B - 1);
			elseif OpCode == 32 then -- FORLOOP
				local A     = Instr.A;
				local Start = REGISTER[A];
				local End   = REGISTER[A + 1];
				local Step  = REGISTER[A + 2] or 1;

				local Current = Start + Step;
				REGISTER[A] = Current;

				if Current <= End then
					PC = PC + Instr.B;
					REGISTER[A + 3] = Current;
				end;
			elseif OpCode == 33 then -- FORPREP
				local A     = Instr.A;
				local Start = REGISTER[A];
				local End   = REGISTER[A + 1];
				local Step  = REGISTER[A + 2] or 1;

				assert(Start, "no for 'initial' value provided");
				assert(End, "no for 'end' value provided");
				assert((Step < 0 and Start > End) or (Start <= End), "for 'initial' cannot be above for 'end'");
				assert((Step ~= 0), "for 'step' cannot be 0 (infinite loop possible)");

				REGISTER[A] = Start - Step;

				PC = PC + Instr.B;
			elseif OpCode == 34 then -- TFORLOOP
				local A        = Instr.A;
				local C        = Instr.C;
				local A2       = A + 2;
				local Iterator = REGISTER[A];
				local State    = REGISTER[A + 1];
				local Index    = REGISTER[A2];

				local Results = Iterator(State, Index);

				for Idx = 1, C, 1 do
					REGISTER[A + Idx] = Results[Idx];
				end;

				local RegisterA3 = REGISTER[A + 3];

				if RegisterA3 then
					REGISTER[A2] = RegisterA3;
				else
					PC = PC + Instr.B;
				end;
			elseif OpCode == 35 then -- SETLIST
				local A = Instr.A;
				local B = Instr.B;
				
				local List   = REGISTER[A];
				local Offset = (Instr.C - 1) * FieldsPerFlush;

				if B == 0 then
					Start = TopIndex - A;
				end;

				for Idx = 1, B do
					List[Offset + Idx] = REGISTER[A + Idx];
				end;
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
