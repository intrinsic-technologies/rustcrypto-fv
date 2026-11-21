import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeMovzxR32M8 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then
    0x0F :: 0xB6 :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x0F :: 0xB6 :: am.modrm (regLow dst) :: am.tail

end X86Proofs
