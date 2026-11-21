import P256.Proofs.Verifying.Core.Finish.Tail.Equal
import P256.Proofs.Verifying.Core.Finish.Tail.Reduce

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar

def equalLayout : StackCallLayout 9992 32 32 32 :=
  ⟨1184,1176,472,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩

theorem equal_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e167)
    (si : t.regValue .rsi = frameBase s)
    (di : t.regValue .rdi = frameBase s+704)
    (input : Nat256At t (frameBase s) x)
    (scalar : Nat256At t (frameBase s+704) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e16c ∧
      memLoad u.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 ∧
      (u.regValue .rax).setWidth 8 = if x == r then 1 else 0 := by
  have outAddr : frameBase s+704 = stackPtr s-472 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨v,run,ready,effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state 0xe167 0x5174 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x132e0 (by decide)) rip
  have frame := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = stackPtr s-1176 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans si
  have vout : v.regValue .rdi = stackPtr s-472 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans outAddr
  have ret : (returnBoundary v).rip = 0x10e16c := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x1132e0 32 32 32 :=
    CalleePre.of_stack pre.toCalleePre equalLayout frame.bindingsSupported frame.machine
      frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp vin vout
      (by rw [ret]; exact inProgram_of_textOffset 0xe16c (by decide))
  have inp : Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    exact ⟨input.1,fun i hi => (scalar_call_byte (frameOffset := 1176)
      (by decide) state effect (by decide) (by decide) hi).trans (input.2 i hi)⟩
  have scal : Nat256At v (v.regValue .rdi) r := by
    rw [vout]
    rw [outAddr] at scalar
    exact ⟨scalar.1,fun i hi => (scalar_call_byte (frameOffset := 1176)
      (by decide) state effect (by decide) (by decide) hi).trans (scalar.2 i hi)⟩
  obtain ⟨u,result,value⟩ := Equal.scalar_equal_correct cp scal inp
  obtain ⟨fuel,run'⟩ := result.execution
  have memory := stack_result_work_frame (frameOffset := 1176) pre.toCalleePre frame result
    vout (by decide) (by decide) (by decide) (by decide)
  refine ⟨1+fuel,u,run.trans run',after_result (frameOffset := 1176) pre.toCalleePre
    frame result (by decide) memory,result.rip.trans ret,?_,?_⟩
  · have addr : frameBase s+384 = stackPtr s-792#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    apply memLoad_congr (n := 64)
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    exact (stack_result_byte (frameOffset := 1176) pre.toCalleePre frame result vout
      (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hi).trans
      (scalar_call_byte (frameOffset := 1176) (by decide) state effect (by decide) (by decide) hi)
  · by_cases eq : x = r
    · subst r
      simpa using value
    · simpa [eq,Ne.symm eq] using value

end P256.Proofs.Verifying.Core.Finish.Tail
