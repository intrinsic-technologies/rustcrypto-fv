import P256.Proofs.Verifying.Wrapper.WorkState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ReturnState.after_callee [Bindings] {initial s t u : RamState}
    {cs : List Component} {outputBytes reserve : Nat}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280)
    (ag : AgreesExcept cs s t) (frame : MemoryWriteFrame s t #v[workRegion initial])
    (rbp : Component.reg 5 ∉ cs) (sp : stackPtr t = stackPtr initial-288)
    (callee : CalleeResult t u (returnBoundary initial) outputBytes reserve)
    (resultFrame : MemoryWriteFrame t u #v[workRegion initial]) : ReturnState initial u := by
  refine ⟨callee.bindingsSupported,callee.machine,callee.loaded,callee.directionFlag,?_,?_,?_,?_,
    fun a ha => callee.allocated a (ag.grow a (state.allocated a ha))⟩
  · change u.regValue .rsp = _
    rw [callee.rsp]
    change stackPtr t+8 = _
    rw [sp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro entry member
    have bound : entry.2 ≤ 40 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (work_read stack resultFrame bound).trans
      ((work_read stack frame bound).trans (state.saved entry member))
  · have h := work_read stack (memoryWriteFrame_trans frame resultFrame) (offset := 0) (by decide)
    change memLoad u.external (stackPtr initial-0#64) 64 =
      memLoad s.external (stackPtr initial-0#64) 64 at h
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · exact (callee.calleeSaved .rbp (by simp)).trans ((ag.read (n := 64) rbp).trans state.rbp)

end P256.Proofs.Verifying.Wrapper
