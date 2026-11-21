import P256.Proofs.Verifying.Wrapper.SignatureCopy.Words
import P256.Proofs.Verifying.Wrapper.SignatureCopy.TailRun

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_correct [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10314b) :
    ∃ fuel u, Advances (returnBoundary initial) fuel s u ∧ ReturnState initial u ∧
      u.RIP = 0x1031a0 ∧ AgreesExcept (components s) s u ∧
      ∀ j < 8, memLoad u.external (stackPtr s+BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (stackPtr s+BitVec.ofNat 64 (80+8*j)) 64 := by
  have stack : Stack.Valid initial 10280 := call.stackAvailable.1
  obtain ⟨fuel,t,run,st⟩ := words_complete call state outside rip
  obtain ⟨fuel',u,run',su,ripU,first,second,ag⟩ :=
    tail_correct call st.toReturnState outside st.rip
  have sp : stackPtr t = stackPtr s :=
    st.agrees.read (n := 64) (r := 4) (by simp [components])
  have wide : AgreesExcept (components s) t u := by
    rw [sp] at ag
    apply ag.widen
    · intro c hc hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp_all [components,Component.isMem]
    · intro a c hc covered
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨i,hi,he⟩ := covered
      exact ⟨.mem (stackPtr s) 64,by simp [components],i,by omega,he⟩
  have full : AgreesExcept (components s) s u :=
    (st.agrees.trans wide).mono (by simp)
  refine ⟨fuel+fuel',u,run.trans run',su,ripU,full,?_⟩
  intro j hj
  by_cases zero : j = 0
  · subst j
    rw [sp] at first
    have source := source_read state call.stackAvailable.1 st.agrees
      (offset := 0) (by decide)
    simpa only [Nat.mul_zero,Nat.add_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
      using first.trans source
  by_cases one : j = 1
  · subst j
    rw [sp] at second
    exact second.trans (source_read state call.stackAvailable.1 st.agrees
      (offset := 8) (by decide))
  · have preserved : memLoad u.external (stackPtr s+BitVec.ofNat 64 (8*j)) 64 =
        memLoad t.external (stackPtr s+BitVec.ofNat 64 (8*j)) 64 := by
      apply memLoad_agrees_apart ag
      intro a len member
      have eq : a = stackPtr t ∧ len = 16 := by simpa using member
      obtain ⟨rfl,rfl⟩ := eq
      rw [sp,state.rsp]
      have address := ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp
        (offset := 8*j) (by decide) (by omega)
      rw [state.rsp] at address
      rw [address]
      exact stack_sub_apart (a := 280) (b := 280-8*j) (na := 16) (nb := 8)
        stack (by decide) (by omega) (by decide) (by omega)
        (Or.inl (by omega))
    exact preserved.trans (st.copied j hj (by omega))

end P256.Proofs.Verifying.Wrapper.SignatureCopy
