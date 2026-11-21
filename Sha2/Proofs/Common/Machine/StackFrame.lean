import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open X86 X86.Machine X86Proofs

structure StackFramePre (p : BitVec 64) (codeLen lo hi : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  align : (rspOf s).toNat % 8 = 0
  bottom : lo ≤ (rspOf s).toNat
  top : (rspOf s).toNat + hi ≤ 2 ^ 32
  present : ∀ i < lo + hi, (s.external[rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  codeLow : p.toNat + codeLen ≤ 2 ^ 32
  codeApart : p.toNat + codeLen ≤ (rspOf s).toNat - lo ∨ (rspOf s).toNat + hi ≤ p.toNat
  tables : (rspOf s).toNat + hi ≤ 0x1000 ∨ 0x3000 + lo ≤ (rspOf s).toNat

end Sha2.Proofs.Common.Machine
