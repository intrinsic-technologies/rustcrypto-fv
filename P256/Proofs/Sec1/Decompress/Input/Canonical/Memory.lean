import X86Proofs.Program.ReadWrite.Bytes
import P256.Proofs.Sec1.Decompress.Input.Canonical.Frame
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem canonical_byte {s t : RamState} (h : AgreesExcept (canonicalFrame s) s t)
    {offset len : Nat} (hlo : 8 ≤ offset) (hgap : offset + len ≤ 184 ∨ 192 ≤ offset)
    (hbound : offset + len ≤ 2^64) {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc hv
  simp only [canonicalFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    apply RangeApart.offsets (stackPtr s) (a := 0) (b := offset) (len := 8) (count := len)
      (by decide) hbound (.inl hlo) j hj i hi
    rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero]
    exact he.symm
  · obtain ⟨j, hj, he⟩ := hv
    apply RangeApart.offsets (stackPtr s) (a := 184) (b := offset) (len := 8) (count := len)
      (by decide) hbound (by omega) j hj i hi
    exact he.symm

theorem canonical_read {s t : RamState} (h : AgreesExcept (canonicalFrame s) s t)
    {offset n : Nat} (hlo : 8 ≤ offset) (hgap : offset + n/8 ≤ 184 ∨ 192 ≤ offset)
    (hbound : offset + n/8 ≤ 2^64) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [canonical_byte h hlo hgap hbound hi]

end P256.Proofs.Sec1.Decompress.Input
