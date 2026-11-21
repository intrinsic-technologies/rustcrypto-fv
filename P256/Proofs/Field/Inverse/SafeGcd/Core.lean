import P256.Proofs.Field.Inverse.SafeGcd.Core.Tail
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input
import P256.Proofs.Field.Inverse.SafeGcd.Core.Output

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem execution_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SafeGcdPre s boundary) :
    ∃ t, CalleeResult s t boundary 40 704 ∧
      Nat256At t (s.regValue .rdi) (Correction.limbs (resultWords (Input.inputs s))).toNat ∧
      memLoad t.external (s.regValue .rdi + 32) 8 = resultChoice (Input.inputs s) ∧
      Refine.Readable t.external (s.regValue .rdi) 33 := by
  obtain ⟨fuel, t, run, ready, post, words, choice, readable, mxcsr, fcw⟩ :=
    advances (code := Machine.fnCode) (initial := s) (fr := Input.activation s)
      (controls := s) (p := Input.inputs s) (boundary := boundary) (fun _ h => h)
      (Input.entry_ready pre) pre.rip (RamWriteFrame.refl _ _)
      (fun x hx he => pre.outerBoundary (he ▸ Input.fnCode_inProgram hx))
      (Or.inl (boundary_ne_program pre.outerBoundary pre.returnInProgram))
      (Input.entry_atoms pre)
  refine ⟨t, Output.result_of_post pre ⟨fuel, run⟩ ready post mxcsr fcw,
    Correction.Execution.output_nat256 words ?_, choice, readable⟩
  exact readable.sub (Nat.le_refl _)
    (by change (s.regValue .rdi).toNat + 32 ≤ (s.regValue .rdi).toNat + 33; omega)

theorem nonzero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : SafeGcdPre s boundary) (ha : Nat256At s (s.regValue .rsi) a)
    (positive : 0 < a) (bound : a < P256.Spec.Operations.domain.p) :
    ∃ t, NonzeroResult s t boundary a := by
  obtain ⟨t, result, words, choice, readable⟩ := execution_correct pre
  obtain ⟨conditions, modulus, argument, scale⟩ := Input.inputs_conditions pre ha bound
  have hp := Arithmetic.result_product (Input.inputs s) conditions modulus
    (by rw [argument]; exact positive)
  have hc := Arithmetic.resultChoice_one (Input.inputs s) conditions modulus
    (by rw [argument]; exact positive)
  rw [Support.packed_limbs, modulus, argument, scale] at hp
  refine ⟨t, result, _, words, hp.1, hp.2, ?_⟩
  apply Output.byte_at readable
  exact choice.trans hc

theorem zero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SafeGcdPre s boundary) (ha : Nat256At s (s.regValue .rsi) 0) :
    ∃ t, ZeroResult s t boundary := by
  obtain ⟨t, result, _, choice, readable⟩ := execution_correct pre
  have hc := Arithmetic.resultChoice_zero (Input.inputs s) (Input.readWords_value ha)
  refine ⟨t, result, Output.byte_at readable ?_⟩
  exact choice.trans hc

end P256.Proofs.Field.Inverse.SafeGcd.Core
