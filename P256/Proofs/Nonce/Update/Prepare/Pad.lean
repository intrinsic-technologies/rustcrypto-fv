import P256.Proofs.Nonce.Update.Prepare.Memory
import P256.Proofs.HMAC.Pad

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {state : State} {loop : HMAC.Pad.Loop}

theorem pad_pre (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : FrameState initial s) (offset : loop.offset = 88)
    (rip : s.RIP = BitVec.ofNat 64 loop.entry) (counter : s.regValue .rax = 3) :
    HMAC.Pad.Pre loop s := by
  have buffer : HMAC.Pad.buffer loop s = stackPtr s + 88 := by
    simp only [HMAC.Pad.buffer, offset, BitVec.ofNat_eq_ofNat]
  refine ⟨⟨?_, ?_⟩, rip, counter⟩
  · rw [buffer]
    exact ScalarFrame.stack_writable pre.callee input (by decide) (by decide) (by decide)
  · intro i hi hp
    apply pre.avoids (Stack.region initial 1856) (by simp) _ ?_ (.inl hp)
    rw [buffer]
    have address : stackPtr s + 88 = stackPtr initial - 592 := ScalarFrame.scalar_stack_address input.rsp (by decide) (by decide : 88 ≤ 680)
    rw [address]
    exact ScalarFrame.stack_contains pre.callee (offset := 592) (len := 64) (by decide) (by decide) ⟨i, hi, rfl⟩

theorem pad_context (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Context initial s state) (offset : loop.offset = 88)
    (ready : ReadyToStep t) (post : HMAC.Pad.Post loop s t) : Context initial t state := by
  apply input.after_agrees pre ready post.agrees
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp [HMAC.Pad.footprint]
  · intro c member a covered
    simp only [HMAC.Pad.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    have buffer : HMAC.Pad.buffer loop s = scratch initial + 88 := by
      simp only [HMAC.Pad.buffer, offset, input.rsp, scratch, BitVec.ofNat_eq_ofNat]
    rw [buffer] at covered
    exact work_contains_scratch pre (by decide) covered

theorem pad_run (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Context initial s state) (offset : loop.offset = 88)
    (rip : s.RIP = BitVec.ofNat 64 loop.entry) (counter : s.regValue .rax = 3)
    (old : UInt8)
    (bytes : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
      (HMAC.keyPad state.key old)) :
    ∃ t, Advances boundary 112 s t ∧ Context initial t state ∧ HMAC.Pad.Post loop s t ∧
      (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes t.external
        (HMAC.keyPad state.key (old ^^^ loop.mask)) := by
  obtain ⟨t, run, ready, _, post⟩ := HMAC.Pad.loop_correct
    (readyToStep input.machine input.bindingsSupported) input.loaded pre.outerBoundary
    (pad_pre pre input.toFrameState offset rip counter)
  have buffer : HMAC.Pad.buffer loop s = scratch initial + 88 := by
    simp only [HMAC.Pad.buffer, offset, input.rsp, scratch, BitVec.ofNat_eq_ofNat]
  refine ⟨t, run, pad_context pre input offset ready post, post, ?_⟩
  simpa only [buffer] using post.keyPad state.key old (by simpa only [buffer] using bytes)

end P256.Proofs.Nonce.Update.Prepare
