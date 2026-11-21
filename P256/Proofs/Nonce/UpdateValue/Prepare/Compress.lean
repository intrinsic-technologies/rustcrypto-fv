import P256.Proofs.Nonce.UpdateValue.Prepare.Compression.Call

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (input : CompressionInput initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t state := by
  obtain ⟨entry, callRun, frame, effect, compressionPre⟩ := Compression.call pre input
  obtain ⟨t, result⟩ := SHA256.compression_correct compressionPre
  have address (offset : Nat) (bound : offset ≤ 488) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (488-offset) := by
    rw [← show stackPtr s = scratch initial from input.rsp]
    exact ScalarFrame.scalar_stack_address input.rsp (by decide) bound
  have addr168 : scratch initial + 168 = stackPtr initial - 320 := address 168 (by decide)
  have addr167 : scratch initial + 167 = stackPtr initial - 321 := address 167 (by decide)
  have addr200 : scratch initial + 200 = stackPtr initial - 288 := address 200 (by decide)
  have addr8 : scratch initial + 8 = stackPtr initial - 480 := address 8 (by decide)
  have output : entry.regValue .rdi = stackPtr initial - 320 := by
    exact ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.destination).trans
      (address 168 (by decide))
  have memory := result.toCalleeResult.stack_frame (savedBytes := 48) pre.stack frame.rsp output
    (by decide) (by decide) (by decide) (by decide)
  have rsp : stackPtr t = scratch initial :=
    (result.rsp.trans (callEffect_stack effect).2).trans input.rsp
  have finalFrame := frame_after_result pre frame result.toCalleeResult memory rsp
  have callDrbg := input.drbg.of_frame pre.stateBounded
    (effect.agrees.memoryWriteFrame (ScalarFrame.scalar_call_writes pre.callee (by decide)
      input.toFrameState))
    (by intro region hr; have h : region = Stack.region initial 1168 := by simpa using hr
        subst region; exact pre.separation)
  have drbg : DrbgAt t (initial.regValue .rdi) state := by
    apply callDrbg.of_frame pre.stateBounded memory
    intro region hr a ha hb
    have h : region = ScalarFrame.workRegion initial 1168 := by simpa using hr
    subst region
    exact pre.separation a ha (work_substack pre hb)
  have copied {offset len : Nat} (bound : offset ≤ 488) (span : len ≤ offset+8)
      (apart : 320 + len ≤ offset ∨ offset + 32 ≤ 320) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (result_stack_byte (stackOffset := 496) (outputOffset := 320) pre result.toCalleeResult frame.rsp output (by decide)
      (by decide) (by omega) (by omega) apart hi span).trans
      (ScalarFrame.scalar_call_byte (frameOffset := 488) (by decide) input.toFrameState effect bound span hi)
  have position : t.external[scratch initial + 167]? = some 0 := by
    have h := copied (offset := 321) (len := 1) (by decide) (by decide) (.inl (by decide))
      0 (by decide)
    simp only [BitVec.add_zero] at h
    rw [addr167]
    have hp := input.position
    rw [addr167] at hp
    exact h.trans hp
  have blocks : loadBytes t.external (scratch initial + 200) 8 = .ok 1 := by
    rw [addr200]
    apply loadBytes_ok_copy (copied (offset := 288) (len := 8) (by decide) (by decide) (.inr (by decide)))
    have hb := input.blocks
    rw [addr200] at hb
    exact hb
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1 + fuel, t, callRun.trans run, ⟨finalFrame, ?_, drbg⟩,
    result.rip.trans (callEffect_stack effect).1, ?_, ?_, ?_⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans input.statePointer)
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp)).trans input.bufferPointer)
  · apply hasBytes_copy input.key
    rw [addr8]
    exact copied (offset := 480) (len := 64) (by decide) (by decide) (.inl (by decide))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨SHA256.remainderBytes_size _, ?_⟩
      intro i
      have bound := i.isLt
      simp only [SHA256.remainderBytes_size, HMAC.keyPad_size, Nat.reduceMod] at bound
      omega
    · simpa only [HMAC.keyPad_size, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd,
        UInt8.reduceOfNat, BitVec.ofNat_eq_ofNat] using position
    · have hh := result.hashWords
      rw [output, ← addr168] at hh
      rw [show scratch initial + 104 + 64 = scratch initial + 168 by
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl]
      exact hh
    · simpa only [HMAC.keyPad_size, Nat.reduceDiv, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.ofNat_eq_ofNat] using blocks

end P256.Proofs.Nonce.UpdateValue.Prepare
