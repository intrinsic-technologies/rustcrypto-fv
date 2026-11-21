import P256.Proofs.Nonce.UpdateValue.Finish.Call
import P256.Proofs.Nonce.UpdateValue.Result

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finalized [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}
    (pre : UpdateValuePre initial boundary state) (input : Called initial s boundary state)
    (result : HMAC.HashCalleeResult s t boundary 672
      (Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key state.value)) :
    Finalized initial t state := by
  have memory : MemoryWriteFrame s t #v[ScalarFrame.workRegion initial 1168] :=
    result.toCalleeResult.stack_frame pre.stack input.rsp input.outputPointer
      (by decide) (by decide) (by decide) (by decide)
  have rsp : stackPtr t = scratch initial := by
    have h : stackPtr t = stackPtr s + 8 := result.rsp
    rw [h, input.rsp]
    change stackPtr initial - 496 + 8 = stackPtr initial - 488
    rw [show (496 : BitVec 64) = 488 + 8 by decide,
      ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have frame := frame_after_result pre input.toFrameState result.toCalleeResult memory rsp
  refine ⟨frame, result.rip.trans input.ret,
    (result.calleeSaved .rbx (by simp)).trans input.valuePointer, ?_, ?_⟩
  · apply input.drbg.of_frame pre.stateBounded memory
    intro r hr a ha hb
    have eq : r = ScalarFrame.workRegion initial 1168 := by simpa using hr
    subst r
    exact pre.separation a ha (work_substack pre hb)
  · simpa only [registerRegion, input.outputPointer, Prepare.Key.output_address] using result.outputBytes

end P256.Proofs.Nonce.UpdateValue.Finish
