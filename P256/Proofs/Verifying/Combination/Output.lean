import P256.Proofs.Verifying.Combination.Output.Transfer
import P256.Proofs.Verifying.Combination.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x1067a3)
    (value : ProjectiveAt t (s.regValue .rdi) point)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 96 8808 ∧ ProjectiveAt u (s.regValue .rdi) point := by
  obtain ⟨a, run, ready, effect⟩ := (mov_r64_r64_effect_step 0x1067a3 0x48 0xd8
    (by simp [RexWPrefix]) rfl).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x67a3 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x67a6 (by decide)))
  have agrees : AgreesExcept [.reg 0, .rip] t a := effect.agrees
  have memory : a.external = t.external := agrees.external (by simp [Component.Covers])
  have stateA := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  obtain ⟨fuel, runS⟩ := execution
  obtain ⟨u, result, memoryU⟩ := epilogue pre stateA effect.rip ⟨fuel+1, runS.trans run⟩
  exact ⟨u, result, value.of_bytes_eq (fun _ _ =>
    congrArg (fun ram : Ram => ram[_]?) (memoryU.trans memory))⟩

end P256.Proofs.Verifying.Combination
