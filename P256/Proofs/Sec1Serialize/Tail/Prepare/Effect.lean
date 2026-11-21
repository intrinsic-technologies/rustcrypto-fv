import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64)

namespace P256.Proofs.Sec1Serialize.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs

def prepareBranchEffect (_ : RamState) : Effect :=
  { rip := 0x111047, flags := some ⟨none, none, none, none, none, none⟩ }

def prepareEncodingEffect (s : RamState) : Effect :=
  { rip := 0x1110cc
    writes := [
      ⟨(.reg 2 : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.reg 5 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 88) : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 96) : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.reg 11 : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.reg 13 : Operand 64), bswap64 ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.reg 12 : Operand 64), bswap64 ((Operand.reg 12 : Operand 64).read s)⟩,
      ⟨(.reg 15 : Operand 64), bswap64 ((Operand.reg 15 : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.reg 3 : Operand 64), bswap64 ((Operand.reg 3 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 200) : Operand 64), bswap64 ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 208) : Operand 64), bswap64 ((Operand.reg 12 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 216) : Operand 64), bswap64 ((Operand.reg 15 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 224) : Operand 64), bswap64 ((Operand.reg 3 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 199) : Operand 8), (4 : BitVec 8)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 232) : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 240) : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 248) : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.reg 0 : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 256) : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩
    ]
    flags := some ⟨none, none, none, none, none, none⟩ }

end P256.Proofs.Sec1Serialize.Prepare
