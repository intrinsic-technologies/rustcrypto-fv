import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill.Call
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill.Memory
import P256.Proofs.HMAC.Finalize.Padding.Bytes
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fill [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Marked initial s boundary message) :
    ∃ t, Padded initial t boundary message := by
  obtain ⟨u, callRun, _, effect, frame⟩ := Fill.call pre state
  have dst : u.regValue .rdi = frameBase initial + 128 + BitVec.ofNat 64 (message.size % 64 + 1) :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have zero : u.regValue .rsi = 0 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.zero
  have count : u.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64) :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.length
  have dstNorm : u.regValue .rdi = stackPtr initial - 1176#64 + BitVec.ofNat 64 (128 + (message.size % 64 + 1)) := by
    simpa only [frameBase, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using dst
  have callPre := Fill.callee_pre pre frame effect.rip dstNorm zero (by
    change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0xd774 (by decide))
  obtain ⟨t, result, zeros, _⟩ := Program.memset_zero_correct callPre
    (by rw [zero]; rfl) count (by omega)
  obtain ⟨fuel, run⟩ := result.execution
  have memory := Fill.result_frame pre frame.rsp dstNorm result
  have finalFrame : Frame initial t :=
    FieldCall.after_result pre.toCalleePre frame result (by decide) memory
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have bytes (i : Nat) (hi : i < 1176) (outside : i ≤ 128 + message.size % 64 ∨ 192 ≤ i) :
      t.external[frameBase initial + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 i]? :=
    (Fill.result_byte pre frame.rsp dstNorm result hi outside).trans
      (ScalarFrame.scalar_call_byte (frameOffset := 1176) (by decide)
        state.toFrameState effect (offset := 1176) (len := 1176) (by decide) (by decide) hi)
  have savedWord {offset : Nat} (lo : 192 ≤ offset) (hi : offset + 8 ≤ 1176) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi'
    apply congrArg (fun o : Option UInt8 => o.getD 0)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact bytes _ (by omega) (.inr (by omega))
  refine ⟨t, {
    toLive := {
      toFrameState := finalFrame
      execution := ?_
      savedKey := (savedWord (by decide) (by decide)).trans state.savedKey
      savedOutput := (savedWord (by decide) (by decide)).trans state.savedOutput
      savedSignature := (savedWord (by decide) (by decide)).trans state.savedSignature
      stackFrame := memoryWriteFrame_trans state.stackFrame
        (memoryWriteFrame_trans
          (effect.agrees.memoryWriteFrame
            (ScalarFrame.scalar_call_writes pre.toCalleePre (by decide) state.toFrameState))
          (work_frame_stack pre.toCalleePre memory)) }
    rip := result.rip.trans (callEffect_stack effect).1
    hash := ?_
    buffer := ?_
    hashPointer := (saved .rbx (by simp)).trans state.hashPointer
    count := (saved .r12 (by simp)).trans state.count
    position := (saved .r15 (by simp)).trans state.position
    remaining := (saved .r14 (by simp)).trans state.remaining }⟩
  · obtain ⟨before, beforeRun⟩ := state.execution
    exact ⟨before + (1 + fuel), beforeRun.trans (callRun.trans run)⟩
  · apply state.hash.copy
    intro i hi
    have h := bytes (192 + i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using h
  · apply SHA256.padded_bytes
    · exact hasBytes_copy state.tail (fun i hi => by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using bytes (128 + i) (by omega) (.inl (by omega)))
    · have h := bytes (128 + message.size % 64) (by omega) (.inl (Nat.le_refl _))
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h.trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using state.marker)
    · intro i hi
      have h := zeros i hi
      simpa only [dst, BitVec.add_assoc, ← BitVec.ofNat_add] using h

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad
