import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXorM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true src :: 0x31 :: am.modrm (regLow src) :: am.tail

def encodeXorM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x31 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x31 :: am.modrm (regLow src) :: am.tail

def encodeXorM8R8 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if src.toNat < 4 ∧ am.rexX = 0 ∧ am.rexB = 0 then 0x30 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x30 :: am.modrm (regLow src) :: am.tail

def encodeXorM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0x80 :: am.modrm 6 :: (am.tail ++ [UInt8.ofBitVec imm])

def encodeCmpM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0x80 :: am.modrm 7 :: (am.tail ++ [UInt8.ofBitVec imm])

end X86Proofs
