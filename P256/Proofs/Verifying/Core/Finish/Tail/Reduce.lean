import P256.Proofs.Verifying.Core.Reduce.Correct
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar

def reduceLayout : StackCallLayout 9992 32 32 104 :=
  ⟨1184,1048,1176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem reduce_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e157)
    (si : t.regValue .rsi = frameBase s+128)
    (di : t.regValue .rdi = frameBase s)
    (input : Nat256At t (frameBase s+128) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e15c ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.r14], u.regValue reg = t.regValue reg) ∧ Nat256At u (frameBase s) (x % Operations.domain.n) ∧
      (∀ offset len : Nat, offset ≤ 1176 → len ≤ offset+8 →
        (offset+32 ≤ 1176 ∨ 1176+len ≤ offset) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u #v[workRegion s 9992] := by
  have inAddr : frameBase s+128 = stackPtr s-1048 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have outAddr : frameBase s = stackPtr s-1176 := rfl
  obtain ⟨v,run,ready,effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state 0xe157 0x4fc4 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x13120 (by decide)) rip
  have frame := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = stackPtr s-1048 :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans si).trans inAddr
  have vout : v.regValue .rdi = stackPtr s-1176 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans outAddr
  have ret : (returnBoundary v).rip = 0x10e15c := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x113120 32 32 104 :=
    CalleePre.of_stack pre.toCalleePre reduceLayout frame.bindingsSupported frame.machine
      frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp vin vout
      (by rw [ret]; exact inProgram_of_textOffset 0xe15c (by decide))
  have inp : Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    rw [inAddr] at input
    exact ⟨input.1,fun i hi => (scalar_call_byte (frameOffset := 1176)
      (by decide) state effect (by decide) (by decide) hi).trans (input.2 i hi)⟩
  obtain ⟨u,result,value⟩ := Core.Reduce.reduce_correct cp inp
  obtain ⟨fuel,run'⟩ := result.execution
  have memory := stack_result_work_frame (frameOffset := 1176) pre.toCalleePre frame result
    vout (by decide) (by decide) (by decide) (by decide)
  have saved (r : Syntax.Reg) (hr : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      u.regValue r = t.regValue r := by
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨1+fuel,u,run.trans run',after_result (frameOffset := 1176) pre.toCalleePre
    frame result (by decide) memory,result.rip.trans ret,?_,?_,?_,
    memoryWriteFrame_trans (field_call_work_frame pre.toCalleePre state
      (by decide) (by decide) effect) memory⟩
  · intro reg hr
    exact saved reg (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
      (show reg = .rbx ∨ reg = .rbp ∨ reg = .r12 ∨ reg = .r13 ∨ reg = .r14 ∨ reg = .r15 from by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> simp))
  · rwa [vout,← outAddr] at value
  · intro offset len ho hl apart i hi
    exact (stack_result_byte (frameOffset := 1176) pre.toCalleePre frame result vout
      (by decide) (by decide) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := 1176) (by decide) state effect ho hl hi)

end P256.Proofs.Verifying.Core.Finish.Tail
