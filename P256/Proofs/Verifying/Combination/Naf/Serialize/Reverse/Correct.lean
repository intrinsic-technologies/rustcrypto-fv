import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.WordsResult
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.OuterBytesResult
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.InnerBytesResult

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem segmentIndex_reverse {i : Nat} (hi : i < 32) :
    segmentIndex 0 6 (segmentIndex 6 11 (segmentIndex 11 16 i)) = 31-i := by
  have h : ∀ j : Fin 32,
      segmentIndex 0 6 (segmentIndex 6 11 (segmentIndex 11 16 j)) = 31-j := by
    decide +kernel
  exact h ⟨i, hi⟩

theorem reverse_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10b1cf reverseBytes) Post := by
  intro s ready loaded pre
  obtain ⟨n₁, a, run₁, ready₁, loaded₁, effect₁⟩ := words_correct boundary outside s ready loaded pre
  have post₁ := words_result pre effect₁
  have pre₁ := pre.after post₁.agrees post₁.rip
  obtain ⟨n₂, b, run₂, ready₂, loaded₂, effect₂⟩ :=
    outerBytes_correct boundary outside a ready₁ loaded₁ pre₁
  have post₂ := outerBytes_result pre₁ effect₂
  have pre₂ := pre₁.after post₂.agrees post₂.rip
  obtain ⟨n₃, c, run₃, ready₃, loaded₃, effect₃⟩ :=
    innerBytes_correct boundary outside b ready₂ loaded₂ pre₂
  have post₃ := innerBytes_result pre₂ effect₃
  refine ⟨n₁+n₂+n₃, c, (run₁.trans run₂).trans run₃, ready₃, loaded₃,
    post₃.rip, footprint_trans (footprint_trans post₁.agrees post₂.agrees) post₃.agrees, ?_⟩
  have rsp₁ : stackPtr a = stackPtr s :=
    post₁.agrees.read (n := 64) (r := 4) (by simp [footprint])
  have rsp₂ : stackPtr b = stackPtr s :=
    (footprint_trans post₁.agrees post₂.agrees).read (n := 64) (r := 4) (by simp [footprint])
  have bytes₂ := post₂.map_bytes (by simpa only [rsp₁] using post₁.bytes)
  have bytes₃ := post₃.map_bytes (by simpa only [rsp₂, rsp₁] using bytes₂)
  rw [rsp₂] at bytes₃
  apply bytes₃.congr
  intro i hi
  simp only [segmentIndex_reverse hi]

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
