import K256.Proofs.Verify.Core.Lincomb.Stack

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

structure FillArguments (fr : Activation) (a : Registers) (dst : BitVec 64) : Prop where
  sp : a[4] = ⟨64, workSp fr - 8⟩
  count : a[2] = ⟨64, 265⟩
  zero : a[6] = ⟨64, 0⟩
  dstReg : a[7] = ⟨64, dst⟩
  df : a[22].get 1 = 0

abbrev PreparesGenerator (fr : Activation) (a : Registers) : Prop :=
  a[3] = ⟨64, 0x12a700⟩ ∧ a[5] = ⟨64, slot fr 0x338⟩ ∧ a[12] = ⟨64, localSp fr + 384⟩ ∧
  a[13] = ⟨64, slot fr 0x228⟩ ∧ a[14] = ⟨64, localSp fr + 416⟩ ∧ a[15] = ⟨64, fr.rsi⟩

end K256.Proofs.Verify.Core.Lincomb
