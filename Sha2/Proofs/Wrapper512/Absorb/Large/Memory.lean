import Sha2.Proofs.Common.Machine.MemoryFrame

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large

open X86 X86.Machine X86Proofs

theorem counter_bytes {s t : RamState} {base offset low high : BitVec 64} {len : Nat}
    (frame : AgreesExcept [.mem (base - low) 8, .mem (base - high) 8, .flags, .rip] s t)
    (apartLow : OffsetsApart (-low) 8 (-offset) len)
    (apartHigh : OffsetsApart (-high) 8 (-offset) len)
    (small : 8 + len < 2^64) :
    ∀ i < len, t.external[base - offset + BitVec.ofNat 64 i]? =
      s.external[base - offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨j, hj, eq⟩ := covered
    exact OffsetsApart.ne apartLow base hj hi small (by simpa only [BitVec.sub_eq_add_neg] using eq.symm)
  · obtain ⟨j, hj, eq⟩ := covered
    exact OffsetsApart.ne apartHigh base hj hi small (by simpa only [BitVec.sub_eq_add_neg] using eq.symm)
  · exact covered
  · exact covered

end Sha2.Proofs.Wrapper512.Absorb.Large
