import P256.Proofs.Verifying.Wrapper.LocalMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (s : RamState) : List Component := [.reg 0,.reg 1,.mem (stackPtr s) 64,.rip]

theorem word_read [Bindings] {initial s t : RamState} {offset query : Nat}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280)
    (ag : AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 offset) 8,.rip] s t)
    (offsetBound : offset+8 ≤ 64) (queryBound : query+8 ≤ 240)
    (apart : offset+8 ≤ query ∨ query+8 ≤ offset) :
    memLoad t.external (stackPtr s+BitVec.ofNat 64 query) 64 =
      memLoad s.external (stackPtr s+BitVec.ofNat 64 query) 64 := by
  apply memLoad_agrees_apart ag
  intro a len member
  have eq : a = stackPtr s+BitVec.ofNat 64 offset ∧ len = 8 := by simpa using member
  obtain ⟨rfl,rfl⟩ := eq
  rw [ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega),
    ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp (by decide) (by omega)]
  exact stack_sub_apart stack (by omega) (by omega) (by omega) (by omega) (by omega)

theorem word_frame {s t : RamState} {offset : Nat}
    (ag : AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 offset) 8,.rip] s t)
    (bound : offset+8 ≤ 64) : AgreesExcept (components s) s t := by
  apply ag.widen
  · intro c hc hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all [components,Component.isMem]
  · intro a c hc covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨i,hi,he⟩ := covered
    refine ⟨.mem (stackPtr s) 64,by simp [components],offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using he

theorem source_read [Bindings] {initial s t : RamState} {offset : Nat}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280)
    (ag : AgreesExcept (components s) s t) (bound : offset+8 ≤ 64) :
    memLoad t.external (stackPtr s+BitVec.ofNat 64 (80+offset)) 64 =
      memLoad s.external (stackPtr s+BitVec.ofNat 64 (80+offset)) 64 := by
  apply memLoad_agrees_apart ag
  intro a len member
  have eq : a = stackPtr s ∧ len = 64 := by simpa [components] using member
  obtain ⟨rfl,rfl⟩ := eq
  rw [state.rsp]
  have address := ScalarFrame.scalar_stack_address (frameOffset := 280) state.rsp
    (offset := 80+offset) (by decide) (by omega)
  rw [state.rsp] at address
  rw [address]
  exact stack_sub_apart (a := 280) (b := 280-(80+offset)) (na := 64) (nb := 8)
    stack (by decide : 280 ≤ 10280) (by omega) (by decide)
    (by omega) (Or.inl (by omega))

end P256.Proofs.Verifying.Wrapper.SignatureCopy
