#[derive(Debug, Clone, Copy)]
pub enum Csr {
    // USER Mode start
    FFlags,
    FRm,
    Fcsr,

    Cycle,
    Time,
    InstRet,
    HPMCounter(u8),

    CycleH,
    TimeH,
    InstRetH,
    HPMCounterH(u8),
    // USER Mode end

    // SUPERVISOR Mode start
    SStatus,
    Sie,
    STVec,
    SCounterEn,

    SEnvCfg,

    SScratch,
    Sepc,
    Scause,
    Stval,
    Sip,

    Satp,

    SContext,
    // SUPERVISOR Mode end

    // Other
    Other(u16),
}

impl From<u16> for Csr {
    fn from(csr: u16) -> Self {
        match csr {
            // USER Mode start
            0x001 => Self::FFlags,
            0x002 => Self::FRm,
            0x003 => Self::Fcsr,

            0xC00 => Self::Cycle,
            0xC01 => Self::Time,
            0xC02 => Self::InstRet,
            0xC03..=0xC1F => Self::HPMCounter((csr & 0xFF) as u8),

            0xC80 => Self::CycleH,
            0xC81 => Self::TimeH,
            0xC82 => Self::InstRetH,
            0xC83..=0xC9F => Self::HPMCounterH((csr & 0xFF) as u8),
            // USER Mode end

            // SUPERVISOR Mode start
            0x100 => Self::SStatus,
            0x104 => Self::Sie,
            0x105 => Self::STVec,
            0x106 => Self::SCounterEn,

            0x10A => Self::SEnvCfg,

            0x140 => Self::SScratch,
            0x141 => Self::Sepc,
            0x142 => Self::Scause,
            0x143 => Self::Stval,
            0x144 => Self::Sip,

            0x180 => Self::Satp,

            0x5A8 => Self::SContext,
            // SUPERVISOR Mode end

            // Other
            other => Self::Other(other),
        }
    }
}
