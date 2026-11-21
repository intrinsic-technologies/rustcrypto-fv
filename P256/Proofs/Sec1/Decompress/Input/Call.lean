import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} {outputBytes reserve outputOffset : Nat}
    (pre : Pre s boundary bytes odd)
    (state : ScalarFrame.FrameState s entry 80 2592 416)
    (output : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (capacity : 416 + reserve ≤ 2592) (outputBound : outputOffset ≤ 2592)
    (outputBelow : outputBytes + 48 ≤ outputOffset)
    (result : CalleeResult entry t boundary outputBytes reserve) : Frame s t := by
  have work := result.stack_frame pre.stack state.rsp output capacity (by decide)
    outputBound outputBelow
  have memory : MemoryWriteFrame entry t
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro a ha
    apply work a
    intro r hr
    have eq : r = ScalarFrame.workRegion s 2592 := by simpa using hr
    subst r
    exact ha _ (by simp)
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (ScalarFrame.output_work_frame pre.toCalleePre memory),
    ?_, ?_, ?_, result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · change stackPtr t = _
    have rsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [rsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.output_work_read pre.toCalleePre (by decide) memory bound
      (by omega)).trans (state.saved e he)
  · have h := ScalarFrame.output_work_read pre.toCalleePre (by decide) memory
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_result_read [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} {outputBytes reserve outputOffset offset n : Nat}
    (pre : Pre s boundary bytes odd)
    (rsp : stackPtr entry = stackPtr s - 416)
    (output : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hout : outputOffset ≤ 2592) (ho : offset ≤ 408) (hlen : n/8 ≤ offset + 8)
    (apart : offset + outputBytes ≤ outputOffset ∨ outputOffset + n/8 ≤ offset) :
    memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) n =
      memLoad entry.external (stackPtr s - BitVec.ofNat 64 offset) n := by
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 = _
  rw [result.stack_byte (frameOffset := 408) pre.stack rsp output
    (by decide) hout ho hlen apart hi]
  rfl

end P256.Proofs.Sec1.Decompress.Input
