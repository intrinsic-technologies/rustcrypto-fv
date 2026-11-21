import P256.Proofs.Scalar.Inverse.Wrapper.Routine
import P256.Proofs.Scalar.Inverse.Wrapper.Output
import P256.Proofs.Scalar.Inverse.Wrapper.Value

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core

theorem execution_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x112e30 32 40 768) :
    ∃ t, CalleeResult s t boundary 40 768 ∧
      Nat256At t (s.regValue .rdi) (Correction.limbs (resultWords (inputs s))).toNat ∧
      memLoad t.external (s.regValue .rdi + 32) 8 = resultChoice (inputs s) ∧
      Refine.Readable t.external (s.regValue .rdi) 33 := by
  obtain ⟨fuel, t, run, ready, post, words, choice, readable, _, mxcsr, fcw⟩ :=
    advances (code := Machine.fnCode) (initial := s) (fr := activation s)
      (p := inputs s) (boundary := boundary) (fun _ h => h)
      (entry_ready pre) pre.rip (RamWriteFrame.refl _ _)
      (fun x hx he => pre.outerBoundary (he ▸ Field.Inverse.SafeGcd.Core.Input.fnCode_inProgram hx))
      (Or.inl (boundary_ne_program pre.outerBoundary pre.returnInProgram))
      (entry_atoms pre)
  refine ⟨t, result_of_post pre ⟨fuel, run⟩ ready post mxcsr fcw,
    Correction.Execution.output_nat256 words ?_, choice, readable⟩
  exact readable.sub (Nat.le_refl _)
    (by change (s.regValue .rdi).toNat + 32 ≤ (s.regValue .rdi).toNat + 33; omega)

theorem nonzero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : CalleePre s boundary 0x112e30 32 40 768) (ha : Nat256At s (s.regValue .rsi) a)
    (positive : 0 < a) (bound : a < P256.Spec.Operations.domain.n) :
    ∃ t, CalleeResult s t boundary 40 768 ∧
      Nat256At t (s.regValue .rdi) (Standards.SECG.ECC.Curve.inverse P256.Spec.Operations.domain.n a) ∧
      t.external[s.regValue .rdi + 32]? = some 1 := by
  obtain ⟨t, result, words, choice, readable⟩ := execution_correct pre
  obtain ⟨hv, hc⟩ := result_value ha positive bound
  refine ⟨t, result, hv ▸ words, ?_⟩
  apply Field.Inverse.SafeGcd.Core.Output.byte_at readable
  exact choice.trans hc

theorem zero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x112e30 32 40 768) (ha : Nat256At s (s.regValue .rsi) 0) :
    ∃ t, CalleeResult s t boundary 40 768 ∧
      t.external[s.regValue .rdi + 32]? = some 0 := by
  obtain ⟨t, result, _, choice, readable⟩ := execution_correct pre
  have hc := result_zero ha
  refine ⟨t, result, Field.Inverse.SafeGcd.Core.Output.byte_at readable ?_⟩
  exact choice.trans hc

end P256.Proofs.Scalar.Inverse.Wrapper
