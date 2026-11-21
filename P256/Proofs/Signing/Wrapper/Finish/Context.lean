import P256.Proofs.Signing.Wrapper.Finish.State
import P256.Proofs.Program.CallPre

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 2048 in
theorem context_pre [Bindings] {initial : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) : Pre initial := by
  obtain ⟨slices,call⟩ := ctx.call
  have valid := call.outputInMemoryIfAccepted rfl
  have separate := call.outputSeparationIfAccepted rfl
  refine ⟨call.stackAvailable.1,valid.2.1,valid.2.2,?_,?_,
    outer_boundary call ctx.machine ctx.bindingsSupported,call.outputSufficesIfAccepted rfl⟩
  · have hp := separate.1 (0 : Fin 5) (4 : Fin 5) (by decide)
    intro a ha hb
    exact hp a ha (stack_contains_callStack hb)
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (separate.2 (outputRegion signingKeyTrySign initial [secret,message]) (by simp)).2
    · exact call_stack_avoids (routine := signingKeyTrySign) call

theorem from_serialized [Bindings] {initial s : RamState} {signature : Nat × Nat}
    (state : SerializedInput initial s signature) : State initial s :=
  ⟨state.bindingsSupported,state.machine,state.loaded,state.directionFlag,state.rsp,
    state.output,state.capacity,state.savedRbx,state.savedR12,state.savedR13,state.savedR14,
    state.savedR15,state.savedRbp,state.returnAddress,state.status,state.allocated⟩

end P256.Proofs.Signing.Wrapper.Finish
