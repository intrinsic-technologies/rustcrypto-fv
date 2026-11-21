import P256.Proofs.Generate.Sampler.Call
import P256.Proofs.Generate.Zero.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

def zeroClobbers (s : RamState) : List Component :=
  [.mem (stackPtr s-272) 8,.mem (stackPtr s-280) 8,.mem (stackPtr s-288) 8,
    .mem (stackPtr s-273) 1,.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.flags,.rip]

theorem zero_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray} {x : Nat}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100c77)
    (left : Nat256At t (stackPtr s-80) x) (right : Nat256At t (stackPtr s-184) 0)
    (di : t.regValue .rdi = stackPtr s-80) (si : t.regValue .rsi = stackPtr s-184) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧ u.RIP = 0x100c7c ∧
      (u.regValue .rax).setWidth 8 = (if x=0 then 1 else 0) ∧
      AgreesExcept (zeroClobbers s) t u := by
  obtain ⟨b,hb,sb,eb⟩ := call_push pre state 0xc77 0x12644 (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0x132c0 (by decide)) rip
  have dib : b.regValue .rdi = stackPtr s-80 :=
    (eb.agrees.read (n := 64) (r := 7) (by simp)).trans di
  have sib : b.regValue .rsi = stackPtr s-184 :=
    (eb.agrees.read (n := 64) (r := 6) (by simp)).trans si
  let layout : StackCallLayout 3624 32 32 32 :=
    ⟨272,184,80,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : CalleePre b boundary 0x1132c0 32 32 32 :=
    CalleePre.of_stack_region pre.stack (pre.avoids _ (by simp)) pre.outerBoundary layout
      sb.bindingsSupported sb.machine sb.directionFlag sb.loaded sb.allocated eb.rip sb.rsp sib dib
      (by change InProgram (stackTop b); rw [(callEffect_stack eb).1]
          exact inProgram_of_textOffset 0xc7c (by decide))
  have lb : Nat256At b (b.regValue .rdi) x := by
    rw [dib]
    exact ⟨left.1,fun i hi => (ScalarFrame.call_byte (frameOffset := 264) (by decide)
      state.rsp eb (by decide) (by decide) hi).trans (left.2 i hi)⟩
  have rb : Nat256At b (b.regValue .rsi) 0 := by
    rw [sib]
    exact ⟨right.1,fun i hi => (ScalarFrame.call_byte (frameOffset := 264) (by decide)
      state.rsp eb (by decide) (by decide) hi).trans (right.2 i hi)⟩
  obtain ⟨u,result,value,agrees,_⟩ := Generate.Zero.zero_correct cp lb rb
  obtain ⟨n,run⟩ := result.execution
  have push : pushAddr t = stackPtr s-272 := by
    simp only [pushAddr,state.rsp,BitVec.sub_sub]; rfl
  refine ⟨1+n,u,hb.trans run,
    return_state pre sb result dib (by decide) (by decide) (by decide),
    result.rip.trans (callEffect_stack eb).1,value,?_⟩
  apply (eb.agrees.trans agrees).mono
  simp only [Generate.Zero.clobbers,Generate.Zero.prefixClobbers,sb.rsp,
    BitVec.sub_sub,BitVec.reduceAdd,pushEffect_components,push]
  simp [zeroClobbers]

end P256.Proofs.Generate.Sampler.Nonzero
