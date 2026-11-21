import P256.Proofs.Verifying.Combination.Loop.MultiPrologue
import P256.Proofs.Verifying.Combination.Loop.MultiIdentitySetup
import P256.Proofs.Verifying.Combination.Loop.MultiIdentityData
import P256.Proofs.Projective.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_identity [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f11a) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧
      w.RIP = 0x10f12e ∧ ProjectiveAt w (stackPtr s - 336) Projective.identity ∧
      AgreesExcept [.reg 7, .reg 1, .reg 6, .mem (stackPtr s - 336) 96, .rip] t w := by
  obtain ⟨fuel, a, run, ready, _, effect⟩ := identitySetup_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf11a identitySetupBytes
      (by decide) (by decide +kernel)) rip
  have frame : AgreesExcept [.reg 7, .reg 1, .reg 6, .rip] t a := effect.agrees
  have stateA := state.after_registers ready frame (by simp [Component.Covers]) (by simp)
  have writes : a.regValue .rdi = stackPtr t + 72 ∧ a.regValue .rcx = 12 ∧
      a.regValue .rsi = 0x202e40 := effect.writes
  have dst : a.regValue .rdi = stackPtr s - 336 :=
    writes.1.trans (scalar_stack_address state.rsp (offset := 72) (by decide) (by decide))
  have value : ProjectiveAt a (a.regValue .rsi) Projective.identity := by
    rw [writes.2.2]
    exact identity_at stateA.loaded
  have source : MemReadable a (a.regValue .rsi) 96 := by
    rw [writes.2.2]
    exact identity_readable stateA.loaded
  have disjoint : (a.regValue .rsi).toNat + 96 ≤ (a.regValue .rdi).toNat ∨
      (a.regValue .rdi).toNat + 96 ≤ (a.regValue .rsi).toNat := by
    rw [writes.2.2, dst]
    exact identity_stack_disjoint pre.toCalleePre (by decide) (by decide)
  obtain ⟨w, runW, stateW, ripW, valueW, frameW⟩ :=
    Copy.copy_to_stack pre.toCalleePre stateA 0xf12b (by decide) (by decide +kernel) effect.rip
      336 (by decide) (by decide) dst writes.2.1 source disjoint value
  exact ⟨fuel+12, w, run.trans runW, stateW, ripW, valueW,
    (frame.trans frameW).mono (by simp)⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
