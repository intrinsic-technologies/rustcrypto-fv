import P256.Proofs.Verifying.Core.Inverse.Contract
import P256.Proofs.Verifying.Core.Prepare.Pointers
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar

def inverseLayout : StackCallLayout 9992 32 40 768 :=
  ⟨1184,440,1048,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem inverse_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (core : Core.Inverse.CoreStage) (positive : 0 < x) (bound : x < Operations.domain.n)
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dc88)
    (si : t.regValue .rsi = frameBase s+736)
    (di : t.regValue .rdi = frameBase s+128)
    (pointers : Prepare.Pointers s t)
    (input : Nat256At t (frameBase s+736) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10dc8d ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s+128) (Standards.SECG.ECC.Curve.inverse Operations.domain.n x) ∧
      u.external[frameBase s+160]? = some 1 ∧
      (∀ offset len : Nat, offset ≤ 1176 → len ≤ offset+8 →
        (offset+40 ≤ 1048 ∨ 1048+len ≤ offset) → ∀ i < len,
        u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  have inAddr : frameBase s+736 = stackPtr s-440 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have outAddr : frameBase s+128 = stackPtr s-1048 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨v,run,ready,effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state 0xdc88 0x5343 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x12fd0 (by decide)) rip
  have frame := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = stackPtr s-440 :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans si).trans inAddr
  have vout : v.regValue .rdi = stackPtr s-1048 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans outAddr
  have ret : (returnBoundary v).rip = 0x10dc8d := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x112fd0 32 40 768 :=
    CalleePre.of_stack pre.toCalleePre inverseLayout frame.bindingsSupported frame.machine
      frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp vin vout
      (by rw [ret]; exact inProgram_of_textOffset 0xdc8d (by decide))
  have inp : Nat256At v (v.regValue .rsi) x := by
    rw [vin]
    rw [inAddr] at input
    exact ⟨input.1,fun i hi => (scalar_call_byte (frameOffset := 1176)
      (by decide) state effect (by decide) (by decide) hi).trans (input.2 i hi)⟩
  obtain ⟨u,result,value,flag⟩ := Core.Inverse.nonzero_correct_of_core core cp inp positive bound
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
    frame result (by decide) memory,result.rip.trans ret,?_,?_,?_,?_,
    memoryWriteFrame_trans (prefix_call pre state effect)
      (prefix_result pre frame result (vout.trans outAddr.symm) (by decide) (by decide))⟩
  · exact ⟨(saved .rbx (by simp)).trans pointers.signature⟩
  · rwa [vout,← outAddr] at value
  · rw [vout,← outAddr] at flag
    have addr : frameBase s+128+32 = frameBase s+160 := by bv_omega
    exact addr ▸ flag
  · intro offset len ho hl apart i hi
    exact (stack_result_byte (frameOffset := 1176) pre.toCalleePre frame result vout
      (by decide) (by decide) ho hl apart hi).trans
      (scalar_call_byte (frameOffset := 1176) (by decide) state effect ho hl hi)

end P256.Proofs.Verifying.Core.Scalars
