import P256.Proofs.Projective.Multiply.Machine.Loop.Finish.Setup
import P256.Proofs.Projective.Multiply.Machine.Loop.Finish.Transfer
import P256.Proofs.Projective.Multiply.Machine.Loop.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective}
    (pre : Pre s boundary) (state : Round.LoopState s t table 64)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 96 1400 ∧
      ProjectiveAt u (s.regValue .rdi) (ProjectiveLoop.linearCombination table (Round.digits s)) := by
  obtain ⟨fuel, v, run, ready, _, effect⟩ := finish_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3425 finishBytes
      (by decide) (by decide +kernel))
    ⟨by simpa using state.rip,
      stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide)⟩
  have frame : AgreesExcept [.reg 6, .reg 1, .reg 0, .reg 7, .rip] t v := effect.agrees
  have memory : v.external = t.external := frame.external (by simp [Component.Covers])
  have stateV := state.toFrameState.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have writes : v.regValue .rsi = stackPtr t + 40 ∧ v.regValue .rcx = 12 ∧
      v.regValue .rax = (Operand.mem (stackPtr t + 16) : Operand 64).read t ∧
      v.regValue .rdi = (Operand.mem (stackPtr t + 16) : Operand 64).read t := effect.writes
  have src : v.regValue .rsi = stackPtr s - 336 :=
    writes.1.trans (scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide))
  have dst : v.regValue .rdi = s.regValue .rdi := by
    rw [writes.2.2.2]
    change (Operand.mem (stackPtr t + BitVec.ofNat 64 16) : Operand 64).read t = _
    rw [scalar_stack_address (frameOffset := 376) state.rsp (by decide) (show 16 ≤ 376 by decide)]
    exact state.output
  have pointV := state.value.of_bytes_eq (t := v) (destination := stackPtr s - 336)
    (fun i hi => by rw [memory])
  obtain ⟨w, runW, stateW, ripW, pointW, _⟩ := transfer pre stateV effect.rip src dst writes.2.1 pointV
  obtain ⟨u, result, memoryU⟩ := epilogue pre stateW ripW (by
    obtain ⟨n, runT⟩ := execution
    exact ⟨n+fuel+12, (runT.trans run).trans runW⟩)
  exact ⟨u, result, pointW.of_bytes_eq (fun i hi => by rw [memoryU])⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
