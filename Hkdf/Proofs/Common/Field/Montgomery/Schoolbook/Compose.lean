import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.EffectCompose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Field.Montgomery.Schoolbook

open X86 X86.Machine X86.UserProcess X86Proofs

theorem memLoad_memStore_rangeApart (mem : Ram) (a b : BitVec 64)
    {n : Nat} (v : BitVec n) (k : Nat) (hap : RangeApart a (n/8) b (k/8)) :
    memLoad (memStore mem a v) b k = memLoad mem b k := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi
  exact hap i hi j hj

end Hkdf.Proofs.Common.Field.Montgomery.Schoolbook
