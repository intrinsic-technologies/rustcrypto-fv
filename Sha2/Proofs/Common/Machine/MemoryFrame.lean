import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open X86 X86.Machine X86Proofs

theorem bytes_of_mem_frame {s t : RamState} {base written offset : BitVec 64}
    {width len : Nat} {components : List Component}
    (frame : AgreesExcept (.mem (base - written) width :: components) s t)
    (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (apart : OffsetsApart (-written) width (-offset) len)
    (small : width + len < 2^64) :
    ∀ i < len, t.external[base - offset + BitVec.ofNat 64 i]? =
      s.external[base - offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covered
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain ⟨j, hj, eq⟩ := covered
    apply OffsetsApart.ne apart base hj hi small
    simpa only [BitVec.sub_eq_add_neg] using eq.symm
  · exact noMem c hc _ covered

end Sha2.Proofs.Common.Machine
