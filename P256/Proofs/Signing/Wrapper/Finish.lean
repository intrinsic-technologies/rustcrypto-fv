import P256.Proofs.Signing.Wrapper.Finish.Accept
import P256.Proofs.Signing.Wrapper.Finish.Context
import P256.Proofs.Signing.Wrapper.Finish.Tag

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_correct : FinishContract := by
  intro bindings initial s secret message signature ctx entry
  have pre := Finish.context_pre ctx
  have state := Finish.from_serialized entry
  obtain ⟨slices,call⟩ := ctx.call
  have boundary := initial_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨b,hb,low,_⟩ := call.returnAddress
  rw [boundary] at hb
  cases hb
  obtain ⟨a,ha,sa,ipa,ma,capacity⟩ :=
    Finish.tag_branch state pre.stack pre.outside entry.rip
  have first : SecretKeyFromBytes.Scalar.Nat256At a (stackPtr initial-456) signature.1 := by
    simpa only [SecretKeyFromBytes.Scalar.Nat256At,ma] using entry.first
  have second : SecretKeyFromBytes.Scalar.Nat256At a (stackPtr initial-424) signature.2 := by
    simpa only [SecretKeyFromBytes.Scalar.Nat256At,ma] using entry.second
  obtain ⟨fuel,t,run,machine,supported,saved,direction,_,frame,output⟩ :=
    Finish.accept pre sa low ipa capacity first second
  obtain ⟨n,prior⟩ := entry.execution
  obtain ⟨total,unique⟩ := ((prior.trans ha).returns run).unique_of_boundary boundary
  refine ⟨total,t,unique,machine,supported,saved,direction,?_,output⟩
  intro x hx
  rw [frame x ?_,ma]
  · apply entry.frame x
    intro r hr hin
    exact hx r (by simpa [wrapperRegions] using Or.inr hr) hin
  · intro r hr hin
    have cases : r = registerRegion initial .rcx 72 ∨ r = Stack.region initial 5112 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact hx (outputRegion signingKeyTrySign initial [secret,message]) (by simp) hin
    · exact hx (callStack signingKeyTrySign initial) (by simp) (stack_contains_callStack hin)

end P256.Proofs.Signing.Wrapper
