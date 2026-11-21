import P256.Proofs.Verifying.Message.Return
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {accepted : Bool} (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (execution : ∃ fuel, Advances boundary fuel initial s)
    (rip : s.RIP = 0x10e194) (result : Core.ResultAt s (initial.regValue .rdi) accepted) :
    ∃ t, CalleeResult initial t boundary 24 9992 ∧
      Core.ResultAt t (initial.regValue .rdi) accepted := by
  obtain ⟨t, runT, readyT, ripT, rspT, memory, agreesT, savedT⟩ :=
    restore_frame pre state rip
  refine ⟨t, {
    execution := ?_
    rip := ripT
    rsp := rspT
    bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported readyT agreesT
    machine := supportedMachine_of_ready_agrees state.machine readyT agreesT
    calleeSaved := savedT
    directionFlag := agreesT.directionFlagClear (by simp) state.directionFlag
    mxcsr := (agreesT.mxcsr (by simp)).trans state.mxcsr
    fp87 := (agreesT.fcw (by simp)).trans state.fp87
    frame := ?_
    loaded := ?_
    allocated := fun a ha => agreesT.grow a (state.allocated a ha)
  }, ?_⟩
  · obtain ⟨fuel, run⟩ := execution
    exact ⟨fuel + 8, run.trans runT⟩
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · exact ⟨by simpa only [memory] using result.tag,
      fun h => by simpa only [memory] using result.error h⟩

end P256.Proofs.Verifying.Message
