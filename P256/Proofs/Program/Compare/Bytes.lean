import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.Ranges

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Program.Compare.Ranges (memReadable_slice)

theorem bytesEqual_prefix {s : RamState} {left right : BitVec 64} {length count : Nat}
    (h : BytesEqual s left right length) (hc : count ≤ length) :
    BytesEqual s left right count := fun i hi ↦ h i (by omega)

theorem BytesEqual.of_agrees {s t : RamState} {left right : BitVec 64} {length : Nat}
    {cs : List Component} (h : BytesEqual s left right length) (ha : AgreesExcept cs s t)
    (hl : ∀ i < length, ∀ c ∈ cs, ¬ c.Covers (left + BitVec.ofNat 64 i))
    (hr : ∀ i < length, ∀ c ∈ cs, ¬ c.Covers (right + BitVec.ofNat 64 i)) :
    BytesEqual t left right length := by
  intro i hi
  change (t.external[left + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[right + BitVec.ofNat 64 i]?).getD 0
  rw [ha.byte (hl i hi), ha.byte (hr i hi)]
  exact h i hi

end P256.Proofs.Program.Compare
