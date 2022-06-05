use super::{Error, Fence, Imm, Instruction, Register, Result};

use std::io::Read;

pub struct Decoder<T: Read>(T);

impl<T: Read> Decoder<T> {
    pub fn new(inner: T) -> Self {
        Self(inner)
    }

    fn rd(inst: u32) -> Register {
        Register::from(((inst >> 7) & 0b11111) as u8)
    }

    fn rs1(inst: u32) -> Register {
        Register::from(((inst >> 15) & 0b11111) as u8)
    }

    fn rs2(inst: u32) -> Register {
        Register::from(((inst >> 20) & 0b11111) as u8)
    }

    fn r(
        inst: u32,
        f: impl FnOnce(Register, Register, Register) -> Instruction,
    ) -> Result<Instruction> {
        Ok(f(Self::rd(inst), Self::rs1(inst), Self::rs2(inst)))
    }

    fn shift(
        inst: u32,
        f: impl FnOnce(Register, Register, u8) -> Instruction,
    ) -> Result<Instruction> {
        let shamt = ((inst >> 20) & 0b111111) as u8;
        Ok(f(Self::rd(inst), Self::rs1(inst), shamt))
    }

    fn u(inst: u32, f: impl FnOnce(Register, u32) -> Instruction) -> Result<Instruction> {
        let imm = inst & !0xfff;
        Ok(f(Self::rd(inst), imm))
    }

    fn i(inst: u32, f: impl FnOnce(Register, Register, Imm) -> Instruction) -> Result<Instruction> {
        let imm = inst >> 20;

        let imm = ((imm as i32) << 20) >> 20;
        Ok(f(Self::rd(inst), Self::rs1(inst), imm))
    }

    fn s(inst: u32, f: impl FnOnce(Register, Register, Imm) -> Instruction) -> Result<Instruction> {
        let imm = ((inst >> 20) & !0b11111) | ((inst >> 7) & 0b11111);

        let imm = ((imm as i32) << 20) >> 20;

        Ok(f(Self::rs1(inst), Self::rs2(inst), imm))
    }

    fn b(inst: u32, f: impl FnOnce(Register, Register, Imm) -> Instruction) -> Result<Instruction> {
        let mut imm = 0;
        imm |= (inst >> 19) & 0b11111111111111111111000000000000;
        imm |= (inst << 4) & 0b00000000000000000000100000000000;
        imm |= (inst >> 20) & 0b00000000000000000000011111100000;
        imm |= (inst >> 7) & 0b00000000000000000000000000011110;

        let imm = ((imm as i32) << 19) >> 19;
        Ok(f(Self::rs1(inst), Self::rs2(inst), imm))
    }

    fn j(inst: u32, f: impl FnOnce(Register, Imm) -> Instruction) -> Result<Instruction> {
        let mut imm = 0;
        imm |= (inst >> 11) & 0b11111111111100000000000000000000;
        imm |= (inst >> 0) & 0b00000000000011111111000000000000;
        imm |= (inst >> 9) & 0b00000000000000000000100000000000;
        imm |= (inst >> 20) & 0b00000000000000000000011111111110;

        let imm = ((imm as i32) << 11) >> 11;
        Ok(f(Self::rd(inst), imm))
    }
}

impl<T: Read> crate::Decode for Decoder<T> {
    type Instruction = Instruction;

    type Error = Error;

    fn decode(&mut self) -> std::result::Result<Self::Instruction, Self::Error> {
        let mut buf = [0u8; 4];
        self.0.read_exact(&mut buf).map_err(Error::IO)?;
        let inst = u32::from_le_bytes(buf);

        let opcode = (inst & 0b1111111) as u8;
        let funct3 = ((inst >> 12) & 0b111) as u8;
        let funct5 = ((inst >> 27) & 0b11111) as u8;
        let funct7 = ((inst >> 25) & 0b1111111) as u8;

        macro_rules! i {
            ($opcode:literal) => {
                ($opcode, _, _, _)
            };

            ($opcode:literal, 3: $funct3:literal) => {
                ($opcode, $funct3, _, _)
            };

            ($opcode:literal, 5: $funct5:literal) => {
                ($opcode, _, $funct5, _)
            };

            ($opcode:literal, 7: $funct7:literal) => {
                ($opcode, _, _, $funct7)
            };

            ($opcode:literal, 3: $funct3:literal, 5: $funct5:literal) => {
                ($opcode, $funct3, $funct5, _)
            };

            ($opcode:literal, 3: $funct3:literal, 7: $funct7:literal) => {
                ($opcode, $funct3, _, $funct7)
            };

            ($opcode:literal, 5: $funct3:literal, 7: $funct7:literal) => {
                ($opcode, _, $funct5, $funct7)
            };

            ($opcode:literal, 3: $funct3:literal, 5: $funct5:literal, 7: $funct7:literal) => {
                ($opcode, $funct3, $funct5, $funct7)
            };

            ($ty:ident: $inst:ident) => {
                Self::$ty(inst, Instruction::$inst)
            };
        }

        match (opcode, funct3, funct5, funct7) {
            // RV32I
            i!(0b0110111) => i!(u: Lui),
            i!(0b0010111) => i!(u: AuiPC),
            i!(0b1101111) => i!(j: Jal),
            i!(0b1100111, 3: 0b000) => i!(i: Jalr),
            i!(0b1100011, 3: 0b000) => i!(b: Beq),
            i!(0b1100011, 3: 0b001) => i!(b: Bne),
            i!(0b1100011, 3: 0b100) => i!(b: Blt),
            i!(0b1100011, 3: 0b101) => i!(b: Bge),
            i!(0b1100011, 3: 0b110) => i!(b: Bltu),
            i!(0b1100011, 3: 0b111) => i!(b: Bgeu),
            i!(0b0000011, 3: 0b000) => i!(i: Lb),
            i!(0b0000011, 3: 0b001) => i!(i: Lh),
            i!(0b0000011, 3: 0b010) => i!(i: Lw),
            i!(0b0000011, 3: 0b100) => i!(i: Lbu),
            i!(0b0000011, 3: 0b101) => i!(i: Lhu),
            i!(0b0100011, 3: 0b000) => i!(s: Sb),
            i!(0b0100011, 3: 0b001) => i!(s: Sh),
            i!(0b0100011, 3: 0b010) => i!(s: Sw),
            i!(0b0010011, 3: 0b000) => i!(i: Addi),
            i!(0b0010011, 3: 0b010) => i!(i: Slti),
            i!(0b0010011, 3: 0b011) => i!(i: Sltiu),
            i!(0b0010011, 3: 0b100) => i!(i: Xori),
            i!(0b0010011, 3: 0b110) => i!(i: ORI),
            i!(0b0010011, 3: 0b111) => i!(i: ANDI),
            i!(0b0010011, 3: 0b001, 7: 0b0000000) => i!(shift: SLLI),
            i!(0b0010011, 3: 0b101, 7: 0b0000000) => i!(shift: SRLI),
            i!(0b0010011, 3: 0b101, 7: 0b0100000) => i!(shift: SRAI),
            i!(0b0110011, 3: 0b000, 7: 0b0000000) => i!(r: ADD),
            i!(0b0110011, 3: 0b000, 7: 0b0100000) => i!(r: SUB),
            i!(0b0110011, 3: 0b001, 7: 0b0000000) => i!(r: SLL),
            i!(0b0110011, 3: 0b010, 7: 0b0000000) => i!(r: SLT),
            i!(0b0110011, 3: 0b011, 7: 0b0000000) => i!(r: SLTU),
            i!(0b0110011, 3: 0b100, 7: 0b0000000) => i!(r: XOR),
            i!(0b0110011, 3: 0b101, 7: 0b0000000) => i!(r: SRL),
            i!(0b0110011, 3: 0b101, 7: 0b0100000) => i!(r: SRA),
            i!(0b0110011, 3: 0b110, 7: 0b0000000) => i!(r: OR),
            i!(0b0110011, 3: 0b111, 7: 0b0000000) => i!(r: AND),
            i!(0b0001111) => Ok(Instruction::FENCE(Fence::decode(inst))),
            i!(0b1110011, 3: 0b000) => match (inst >> 20) & 0b1 == 0b1 {
                false => Ok(Instruction::ECALL),
                true => Ok(Instruction::EBREAK),
            },

            _ => Err(Error::InvalidInstruction {
                inst,
                opcode,
                funct3,
                funct5,
                funct7,
            }),
        }
    }
}