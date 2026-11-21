import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Stages
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Prefix

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prefix_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : First s t v) :
    ∃ fuel u, Advances boundary fuel t u ∧ ScalarFrame.FrameState s u 32 112 112 ∧
      (prefixEffect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := prefix_block boundary pre.outerBoundary t
    (readyToStep state.frame.machine state.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.frame.loaded) 0x13490 prefixBytes
      (by decide) (by decide +kernel)) state.rip
  refine ⟨fuel, u, run, state.frame.after_registers ready effect.agrees ?_ ?_, effect⟩
  · simp [prefixEffect, Effect.components, Component.Covers]
  · simp [prefixEffect, Effect.components]

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
