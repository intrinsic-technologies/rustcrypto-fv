import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Output

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar


theorem execution_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, CalleeResult s t boundary 32 56 ∧
      Nat256At t (s.regValue .rdi) (limbs (correctedWords (inputs s))).toNat := by
  obtain ⟨fuel, t, run, ready, post, words, readable, mxcsr, fcw⟩ :=
    Execution.correction_advances (code := Execution.Machine.fnCode)
      (initial := s) (fr := Execution.activation s) (controls := s) (p := inputs s)
      (boundary := boundary) (fun _ h => h)
      (Execution.entry_ready pre) pre.rip (RamWriteFrame.refl _ _) (fun x hx he =>
        pre.outerBoundary (he ▸ Execution.fnCode_inProgram hx))
      (Or.inl (boundary_ne_program pre.outerBoundary pre.returnInProgram))
      (Execution.entry_atoms pre)
  exact ⟨t, Execution.result_of_post pre ⟨fuel, run⟩ ready post mxcsr fcw,
    Execution.output_nat256 words readable⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction
