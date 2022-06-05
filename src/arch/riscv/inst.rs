use super::{Csr, Fence, Register};

use std::sync::atomic::Ordering;

pub type Imm = i32;

#[derive(Debug)]
pub enum Instruction {
    // RV32I
    Lui(Register, u32),
    AuiPC(Register, u32),
    Jal(Register, Imm),
    Jalr(Register, Register, Imm),
    Beq(Register, Register, Imm),
    Bne(Register, Register, Imm),
    Blt(Register, Register, Imm),
    Bge(Register, Register, Imm),
    Bltu(Register, Register, Imm),
    Bgeu(Register, Register, Imm),
    Lb(Register, Register, Imm),
    Lh(Register, Register, Imm),
    Lw(Register, Register, Imm),
    Lbu(Register, Register, Imm),
    Lhu(Register, Register, Imm),
    Sb(Register, Register, Imm),
    Sh(Register, Register, Imm),
    Sw(Register, Register, Imm),
    Addi(Register, Register, Imm),
    Slti(Register, Register, Imm),
    Sltiu(Register, Register, Imm),
    Xori(Register, Register, Imm),
    ORI(Register, Register, Imm),
    ANDI(Register, Register, Imm),
    SLLI(Register, Register, u8),
    SRLI(Register, Register, u8),
    SRAI(Register, Register, u8),
    ADD(Register, Register, Register),
    SUB(Register, Register, Register),
    SLL(Register, Register, Register),
    SLT(Register, Register, Register),
    SLTU(Register, Register, Register),
    XOR(Register, Register, Register),
    SRL(Register, Register, Register),
    SRA(Register, Register, Register),
    OR(Register, Register, Register),
    AND(Register, Register, Register),
    FENCE(Fence),
    ECALL,
    EBREAK,

    // RV64I
    Lwu(Register, Register, Imm),
    Ld(Register, Register, Imm),
    Sd(Register, Register, Imm),
    Addiw(Register, Register, Imm),
    SLLIW(Register, Register, u8),
    SRLIW(Register, Register, u8),
    SRAIW(Register, Register, u8),
    ADDW(Register, Register, Register),
    SUBW(Register, Register, Register),
    SLLW(Register, Register, Register),
    SRLW(Register, Register, Register),
    SRAW(Register, Register, Register),

    // RV32/RV64 Zicsr
    CsrRw(Register, Register, Csr),
    CsrRs(Register, Register, Csr),
    CsrRc(Register, Register, Csr),
    CsrRwi(Register, u32, Csr),
    CsrRsi(Register, u32, Csr),
    CsrRci(Register, u32, Csr),

    // RV32M
    Mul(Register, Register, Register),
    Mulh(Register, Register, Register),
    Mulhsu(Register, Register, Register),
    Mulhu(Register, Register, Register),
    Div(Register, Register, Register),
    Divu(Register, Register, Register),
    Rem(Register, Register, Register),
    Remu(Register, Register, Register),

    // RV64M
    Mulw(Register, Register, Register),
    Divw(Register, Register, Register),
    Divuw(Register, Register, Register),
    Remw(Register, Register, Register),
    Remuw(Register, Register, Register),

    // RV32A
    LrW(Register, Register, Register, Ordering),
    ScW(Register, Register, Register, Ordering),
    AMOSwapW(Register, Register, Register, Ordering),
    AMOAddW(Register, Register, Register, Ordering),
    AMOXorW(Register, Register, Register, Ordering),
    AMOAndW(Register, Register, Register, Ordering),
    AMOOrW(Register, Register, Register, Ordering),
    AMOMinW(Register, Register, Register, Ordering),
    AMOMaxW(Register, Register, Register, Ordering),
    AMOMinUW(Register, Register, Register, Ordering),
    AMOMaxUW(Register, Register, Register, Ordering),
}
