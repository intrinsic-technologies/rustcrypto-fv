import P256.Proofs.Nonce.Initialize.Seed.UpdatePre
import P256.Proofs.Program.FieldCall.Result

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Seeded [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (state : Nonce.State) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107c1a
  order : s.regValue .r15 = orderAddress
  output : s.regValue .r14 = initial.regValue .rdi
  drbg : DrbgAt s (stackPtr s + 8) state

theorem update_result [Bindings] {initial s entry t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value : Nat} {updated : Nonce.State}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (state : UpdateReady initial s boundary orderAddress value)
    (run : Advances boundary 1 s entry) (ready : ReadyToStep entry)
    (effect : (callEffect (fun _ => 0x109f30) 0x107c1a s).Holds s entry)
    (result : DrbgCalleeResult entry t boundary 1856 updated) :
    Seeded initial t boundary orderAddress updated := by
  have frame : Stage initial entry boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have dst : entry.regValue .rdi = stackPtr initial - 272 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans state.destination
    change entry.regValue .rdi = stackPtr s + 8 at h
    rw [state.stage.rsp] at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have mem := FieldCall.stack_result_work_frame (frameOffset := 280) pre.toCalleePre
    frame.toFrameState result.toCalleeResult dst (by decide) (by decide) (by decide) (by decide)
  have tf := FieldCall.after_result (frameOffset := 280) pre.toCalleePre frame.toFrameState
    result.toCalleeResult (by decide) mem
  obtain ⟨n, hn⟩ := frame.execution
  obtain ⟨m, hm⟩ := result.execution
  refine ⟨⟨tf, n + m, hn.trans hm⟩, result.rip.trans (callEffect_stack effect).1,
    (result.calleeSaved .r15 (by simp)).trans ((effect.agrees.read (n := 64) (r := 15)
      (by simp [pushEffect_components])).trans state.order),
    (result.calleeSaved .r14 (by simp)).trans ((effect.agrees.read (n := 64) (r := 14)
      (by simp [pushEffect_components])).trans state.outputPointer), ?_⟩
  have addr : stackPtr t + 8 = entry.regValue .rdi := by
    rw [dst, tf.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  simpa only [addr] using result.stateBytes

end P256.Proofs.Nonce.Initialize.Seed
