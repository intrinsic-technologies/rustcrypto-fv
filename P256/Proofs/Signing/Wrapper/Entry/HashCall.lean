import P256.Proofs.Signing.Wrapper.Entry.HashCall.Read
import P256.Proofs.Signing.Wrapper.Entry.Stages
import P256.Proofs.Signing.Wrapper.Entry.Input

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.HashCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct : HashCallContract := by
  intro bindings initial s secret message ctx state
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨fuel,t,run,st,rip,pointer,length,_,ag⟩ :=
    message_read call state.toState state.frame outside state.rip state.pointers state.lengths
  have memory := ag.external (by simp [Component.Covers])
  have scalar : Nat256At t (stackPtr initial-152) (Ecdsa.secretValue secret) := by
    exact ⟨state.scalar.1,fun i hi => by rw [memory]; exact state.scalar.2 i hi⟩
  have valid := (arguments_iff secret message).mp call.argumentsValid
  refine ⟨fuel,t,run,⟨⟨st,ctx,rip,pointer,length,?_,?_⟩,scalar,?_,?_⟩⟩
  · simpa only [memory] using state.output
  · simpa only [memory] using state.capacity
  · rw [secretValue_eq call.argumentsValid]
    exact valid.2.1
  · rw [secretValue_eq call.argumentsValid]
    exact valid.2.2

end P256.Proofs.Signing.Wrapper.Entry.HashCall
