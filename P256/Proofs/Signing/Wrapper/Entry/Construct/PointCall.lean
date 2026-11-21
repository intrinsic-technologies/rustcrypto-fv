import P256.Proofs.Signing.Wrapper.Entry.Construct.Memory
import P256.Proofs.PublicPoint.Correct
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar

def pointLayout : StackCallLayout 5112 32 65 3352 :=
  ⟨528,344,424,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem point_call [bindings : Bindings] {initial s : RamState} {secret message : ByteArray}
    {d : Nat} (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x10264b) (rdi : s.regValue .rdi=stackPtr initial-424)
    (rsi : s.regValue .rsi=stackPtr initial-344)
    (input : Nat256At s (stackPtr initial-344) d)
    (scalar : Nat256At s (stackPtr initial-520) d) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      t.RIP=0x102650 ∧ Nat256At t (stackPtr initial-520) d ∧
      (∀ r ∈ [Syntax.Reg.r12,.r13,.r15],t.regValue r=s.regValue r) ∧
      (∀ off : Nat, off ∈ [192,200,208] →
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64) := by
  obtain ⟨slices,call⟩ := ctx.call
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    call_stack_avoids (routine := signingKeyTrySign) call
  obtain ⟨a,runA,readyA,_,effect,memory⟩ := call_rel32_exists stack avoids outside
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    520 0x264b 0xc0a0 state.rsp rip (by decide) (by decide) (by decide)
    (by decide +kernel) (inProgram_of_textOffset 0xe6f0 (by decide))
  have push : pushAddr s=stackPtr initial-528#64 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]; rfl
  have ag : AgreesExcept [.reg 4,.mem (stackPtr initial-528) 8,.rip] s a := by
    simpa only [pushEffect_components,push,BitVec.ofNat_eq_ofNat] using effect.agrees
  have sp : stackPtr a=stackPtr initial-528#64 := effect.writes.1.trans push
  have sa : State initial a 528 := state.after_effect call runA readyA ag (by
    intro c hc addr ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨workRegion initial,by simp,work_contains stack (by decide) (by decide) ha⟩)
    sp (by simp)
  have preserve {off : Nat} (bound : off≤520) (lower : 24≤off) {i : Nat} (hi : i<32) :
      a.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?=
        s.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
    apply ag.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨j,hj,eq⟩ := ha
    exact stack_sub_apart stack (a := off) (b := 528) (by omega) (by decide)
      (by omega) (by decide) (Or.inr (by omega)) i hi j hj eq
  have da : a.regValue .rdi=stackPtr initial-424 :=
    (ag.read (n := 64) (r := 7) (by simp)).trans rdi
  have ia : a.regValue .rsi=stackPtr initial-344 :=
    (ag.read (n := 64) (r := 6) (by simp)).trans rsi
  have ret : (returnBoundary a).rip=0x102650 := (callEffect_stack effect).1
  have pre : CalleePre a (returnBoundary initial) 0x10e6f0 32 65 3352 :=
    CalleePre.of_stack_region stack avoids outside pointLayout sa.bindingsSupported
      sa.machine sa.directionFlag sa.loaded sa.allocated effect.rip sa.rsp ia da
      (ret ▸ inProgram_of_textOffset 0x2650 (by decide))
  have inputA : Nat256At a (a.regValue .rsi) d := by
    rw [ia]
    exact ⟨input.1,fun i hi => (preserve (off := 344) (by decide) (by decide) hi).trans (input.2 i hi)⟩
  obtain ⟨t,result,_⟩ := PublicPoint.public_point_correct bindings a _ d pre inputA
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨1+fuel,t,runA.trans run,sa.after_callee call result da
    (by decide) (by decide) (by decide) (by decide),result.rip.trans ret,?_,?_,?_⟩
  · refine ⟨scalar.1,fun i hi => ?_⟩
    exact (result.stack_byte stack (frameOffset := 520) sa.rsp da (offset := 520)
      (len := 32) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hi).trans
      ((preserve (off := 520) (by decide) (by decide) hi).trans (scalar.2 i hi))
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (result.calleeSaved .r12 (by simp)).trans (ag.read (n := 64) (r := 12) (by simp))
    · exact (result.calleeSaved .r13 (by simp)).trans (ag.read (n := 64) (r := 13) (by simp))
    · exact (result.calleeSaved .r15 (by simp)).trans (ag.read (n := 64) (r := 15) (by simp))
  · intro off member
    have bounds : 192 ≤ off ∧ off ≤ 208 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> omega
    apply memLoad_congr
    intro i hi
    change (t.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?).getD 0 =
      (s.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?).getD 0
    rw [(result.stack_byte stack (frameOffset := 520) (outputOffset := 424) sa.rsp da (offset := off)
      (len := 8) (by decide) (by decide) (by omega) (by omega) (.inl (by omega)) hi).trans
      (preserve (off := off) (by omega) (by omega) (by omega))]

end P256.Proofs.Signing.Wrapper.Entry.Construct
