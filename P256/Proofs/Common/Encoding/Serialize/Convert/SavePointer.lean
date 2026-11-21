import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem read_mem_of_agrees {s t : RamState} {cs : List Component} {n : Nat}
    (h : AgreesExcept cs s t) (address : BitVec 64)
    (ha : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (address + BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand n).read t = (Operand.mem address : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[address + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[address + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte (ha i hi)]

end P256.Proofs.Common.Encoding.Serialize
