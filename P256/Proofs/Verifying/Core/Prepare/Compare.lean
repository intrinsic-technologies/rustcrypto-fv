import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Generate.Zero.Correct
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar

def compareClobbers (s : RamState) : List Component :=
  [.mem (stackPtr s-1184) 8,.mem (stackPtr s-1192) 8,.mem (stackPtr s-1200) 8,
    .mem (stackPtr s-1185) 1,.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.flags,.rip]

theorem compare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (second : Bool)
    (rip : t.RIP = if second then 0x10db5f else 0x10dab2)
    (left : Nat256At t (stackPtr s-1176) x)
    (right : Nat256At t (stackPtr s-1048) 0)
    (di : t.regValue .rdi = stackPtr s-1176)
    (si : t.regValue .rsi = stackPtr s-1048) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧
      u.RIP = (if second then 0x10db64 else 0x10dab7) ∧
      (u.regValue .rax).setWidth 8 = (if x=0 then 1 else 0) ∧
      AgreesExcept (compareClobbers s) t u := by
  let offset : Nat := if second then 0xdb5f else 0xdab2
  let disp : BitVec 32 := if second then 0x575c else 0x5809
  obtain ⟨b,hb,rb,eb⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state offset disp (by cases second <;> decide)
    (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)
    (by cases second <;> exact inProgram_of_textOffset 0x132c0 (by decide))
    (by cases second <;> exact rip)
  have sb := state.after_call pre.toCalleePre (by decide) (by decide) rb eb
  have dib : b.regValue .rdi = stackPtr s-1176 :=
    (eb.agrees.read (n := 64) (r := 7) (by simp)).trans di
  have sib : b.regValue .rsi = stackPtr s-1048 :=
    (eb.agrees.read (n := 64) (r := 6) (by simp)).trans si
  let layout : StackCallLayout 9992 32 32 32 :=
    ⟨1184,1048,1176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  have cp : CalleePre b boundary 0x1132c0 32 32 32 :=
    CalleePre.of_stack pre.toCalleePre layout
      sb.bindingsSupported sb.machine sb.directionFlag sb.loaded sb.allocated
      (by cases second <;> exact eb.rip) sb.rsp sib dib
      (by change InProgram (stackTop b); rw [(callEffect_stack eb).1]
          cases second
          · exact inProgram_of_textOffset 0xdab7 (by decide)
          · exact inProgram_of_textOffset 0xdb64 (by decide))
  have lb : Nat256At b (b.regValue .rdi) x := by
    rw [dib]
    exact ⟨left.1,fun i hi => (scalar_call_byte (frameOffset := 1176) (by decide)
      state eb (by decide) (by decide) hi).trans (left.2 i hi)⟩
  have rb : Nat256At b (b.regValue .rsi) 0 := by
    rw [sib]
    exact ⟨right.1,fun i hi => (scalar_call_byte (frameOffset := 1176) (by decide)
      state eb (by decide) (by decide) hi).trans (right.2 i hi)⟩
  obtain ⟨u,result,value,agrees,_⟩ := Generate.Zero.zero_correct cp lb rb
  obtain ⟨n,run⟩ := result.execution
  have push : pushAddr t = stackPtr s-1184 := scalar_call_address state
  refine ⟨1+n,u,hb.trans run,
    after_result pre.toCalleePre sb result (by decide)
      (stack_result_work_frame pre.toCalleePre sb result dib
        (by decide) (by decide) (by decide) (by decide)),?_,value,?_⟩
  · have h := result.rip.trans (callEffect_stack eb).1
    cases second <;> exact h
  · apply (eb.agrees.trans agrees).mono
    simp only [Generate.Zero.clobbers,Generate.Zero.prefixClobbers,sb.rsp,
      BitVec.sub_sub,pushEffect_components,push]
    simp [compareClobbers]

end P256.Proofs.Verifying.Core.Prepare
