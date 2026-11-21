import P256.Proofs.Sec1.Decompress.Select.ZeroEntry
import P256.Proofs.Sec1.Decompress.Select.CopyEntry

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zero_byte {s t u : RamState} (frame : AgreesExcept (zeroComponents s) t u)
    {offset len : Nat} (apart : OffsetsApart (-(216 : BitVec 64)) 32 (-BitVec.ofNat 64 offset) len) (bound : 32 + len < 2^64)
    {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply frame.byte
  intro c hc ha
  simp only [zeroComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ha.elim
  · obtain ⟨j, hj, he⟩ := ha
    apply OffsetsApart.ne apart (stackPtr s) hj hi bound
    simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem copy_byte {s t u : RamState} (frame : AgreesExcept (copyComponents s) t u)
    {offset len : Nat} (apart : OffsetsApart (-(408 : BitVec 64)) 32 (-BitVec.ofNat 64 offset) len) (bound : 32 + len < 2^64)
    {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply frame.byte
  intro c hc ha
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  apply OffsetsApart.ne apart (stackPtr s) hj hi bound
  simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem stack_read_of_bytes {s t u : RamState} {offset n : Nat}
    (bytes : ∀ i < n/8, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun b : Option UInt8 => b.getD 0) (bytes i hi)

end P256.Proofs.Sec1.Decompress.Select
