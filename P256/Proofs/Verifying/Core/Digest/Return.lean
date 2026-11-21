import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.ReadBe.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem readBe_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : Core.Pre s boundary)
    (state : ScalarFrame.FrameState s entry 24 9992 1184) (result : ReadBe.Result entry t boundary input)
    (destination : entry.regValue .rdx = stackPtr s - 1176) : Frame s t := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdx).toNat = (stackPtr s).toNat - 1176 := by
    rw [destination]
    exact stack_sub_toNat pre.stack (by decide)
  have memory : MemoryWriteFrame entry t #v[registerRegion s .rdi 24, workRegion s 9992] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    apply ha (workRegion s 9992) (by simp)
    have hr' : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 := by
      simpa using hr
    change (stackPtr s).toNat - 9992 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 9992 + 9944
    rcases hr' with rfl | rfl
    · change (entry.regValue .rdx).toNat ≤ a.toNat ∧
        a.toNat < (entry.regValue .rdx).toNat + 32 at hin
      rw [dst] at hin
      constructor <;> omega
    · change (stackPtr entry).toNat - 128 ≤ a.toNat ∧
        a.toNat < (Stack.region entry 128).start + (Stack.region entry 128).size at hin
      rw [stack_region_end] at hin
      change (stackPtr entry).toNat - 128 ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8 at hin
      rw [sp] at hin
      constructor <;> omega
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre.toCalleePre memory), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hr : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hr, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre.toCalleePre (by decide) memory bound (by omega)).trans (state.saved e he)
  · have h := output_work_read pre.toCalleePre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Verifying.Core.Digest
