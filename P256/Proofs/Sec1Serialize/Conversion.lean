import P256.Proofs.Sec1Serialize.Composition
import P256.Proofs.Sec1Serialize.Conversion.X
import P256.Proofs.Sec1Serialize.Conversion.Y

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem conversion_correct [bindings : Bindings] : ConversionCorrect bindings := by
  intro s t boundary x y pre state rip inputX inputY rsi r14 rdi compress
  have stage : Conversion.Stage s t t boundary := ⟨state, 0, by simp⟩
  obtain ⟨v, stateV, ripV, x0, x1, x2, x3, r9V, r14V, rdiV, memoryV⟩ :=
    Conversion.convert_x_correct pre stage rip inputX rsi r14
  have inputYV : Field.MontgomeryAt v (s.regValue .rsi + 32) y :=
    inputY.of_bytes_eq (by intro i hi; rw [memoryV])
  have compressV : compressionFlag s v := by
    change memLoad v.external _ 32 = 0
    rw [memoryV]
    exact compress
  obtain ⟨u, stateU, ripU, converted, rdiU, compressU, saved⟩ :=
    Conversion.convert_y_correct pre stateV ripV inputYV x0 x1 x2 x3 r9V r14V
      (rdiV.trans rdi) compressV
  obtain ⟨fuel, run⟩ := stateU.execution
  exact ⟨fuel, u, run, stateU.toFrameState, ripU, converted, rdiU, compressU, saved⟩

end P256.Proofs.Sec1Serialize
