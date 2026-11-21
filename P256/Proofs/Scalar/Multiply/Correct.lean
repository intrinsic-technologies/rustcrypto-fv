import P256.Proofs.Scalar.Multiply.Output
import P256.Proofs.Scalar.Multiply.Barrett
import P256.Proofs.Scalar.Multiply.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Schoolbook (packFour)

theorem barrett_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {lo hi : Nat}
    (pre : BarrettPre s boundary)
    (low : Nat256At s (s.regValue .rsi) lo) (high : Nat256At s (s.regValue .rdx) hi) :
    ∃ t, CalleeResult s t boundary 32 112 ∧
      Nat256At t (s.regValue .rdi) ((lo + 2^256 * hi) % P256.Spec.Operations.domain.n) := by
  obtain ⟨fuel, t, run, ready, post, words, readable, mxcsr, fcw⟩ :=
    Barrett.barrett_advances (code := Barrett.Machine.fnCode)
      (initial := s) (fr := Adapter.activation s) (controls := s) (p := Adapter.inputs s)
      (boundary := boundary) (fun _ h => h)
      (Adapter.entry_ready pre) pre.rip (RamWriteFrame.refl _ _) (fun x hx he =>
        pre.outerBoundary (he ▸ P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.fnCode_inProgram hx))
      (Or.inl (boundary_ne_program pre.outerBoundary pre.returnInProgram))
      (Adapter.entry_atoms pre)
  have output := Adapter.output_nat256 words readable
  have value : packFour ((Barrett.reducedWords (Adapter.inputs s)).map BitVec.toNat) =
      (lo + 2^256 * hi) % P256.Spec.Operations.domain.n := by
    calc
      _ = (packFour ((Adapter.inputs s).low.map BitVec.toNat) +
          2^256 * packFour ((Adapter.inputs s).high.map BitVec.toNat)) %
          P256.Spec.Operations.domain.n := Arithmetic.resultWords_correct (Adapter.inputs s)
      _ = _ := by
        simp only [Adapter.inputs, Adapter.readWords_value low, Adapter.readWords_value high]
  rw [value] at output
  exact ⟨t, Adapter.result_of_post pre ⟨fuel, run⟩ ready post mxcsr fcw, output⟩

end P256.Proofs.Scalar.Multiply
