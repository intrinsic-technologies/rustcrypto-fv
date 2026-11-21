import P256.Proofs.Nonce.Update.State
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame

theorem frame_after_result [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes outerReserve callBytes reserve : Nat}
    {depth newDepth : BitVec 64} {inputRegister outputRegister : Syntax.Reg}
    (pre : CalleePre initial boundary entry inputBytes outputBytes outerReserve inputRegister)
    (large : 48 ≤ outerReserve)
    (frame : ScalarFrame.FrameState initial s outputBytes outerReserve depth)
    (result : CalleeResult s t boundary callBytes reserve outputRegister)
    (memory : MemoryWriteFrame s t
      #v[registerRegion initial .rdi outputBytes, workRegion initial outerReserve])
    (rsp : stackPtr t = stackPtr initial - newDepth) :
    ScalarFrame.FrameState initial t outputBytes outerReserve newDepth := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (frame.allocated a ha),
    memoryWriteFrame_trans frame.frame (output_work_frame pre memory), rsp, ?_, ?_,
    result.mxcsr.trans frame.mxcsr, result.fp87.trans frame.fp87⟩
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre large memory bound (by omega)).trans (frame.saved e he)
  · have h := output_work_read pre large memory (offset := 0) (n := 64)
      (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress

end P256.Proofs.Nonce.Update
