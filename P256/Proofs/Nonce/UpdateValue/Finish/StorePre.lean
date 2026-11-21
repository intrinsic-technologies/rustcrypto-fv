import P256.Proofs.Nonce.UpdateValue.Finish.StoreRun
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}

theorem store_pre (pre : UpdateValuePre initial boundary state)
    (input : Finalized initial s state) : StorePre s := by
  have pointer : valuePointer s = initial.regValue .rdi + 32 := input.valuePointer
  refine ⟨input.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_readable pre.callee input.toFrameState (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_writable pre.callee input.toFrameState (by decide) (by decide) (by decide)
  · intro i hi off len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) (by omega)
  · have writable := (ScalarFrame.output_writable pre.callee (by decide) input.allocated).add (len := 32) 32 (by decide)
    intro i hi
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact writable.add _ (by decide)
  · intro i hi off len bound
    obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, k ≤ 24 ∧ i = BitVec.ofNat 64 k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨24, by decide, rfl⟩
    intro a ha b hb eq
    apply ScalarFrame.output_code pre.callee (by omega : off + len ≤ 118431)
      (32 + k + a) (by omega) b hb
    simpa only [pointer, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using eq
  · intro i hi j hj a ha b hb eq
    rw [pointer] at eq
    obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, k ≤ 24 ∧ i = BitVec.ofNat 64 k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨24, by decide, rfl⟩
    obtain ⟨l, hl, rfl⟩ : ∃ l : Nat, l ≤ 96 ∧ j = BitVec.ofNat 64 l := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · exact ⟨72, by decide, rfl⟩
      · exact ⟨80, by decide, rfl⟩
      · exact ⟨88, by decide, rfl⟩
      · exact ⟨96, by decide, rfl⟩
    have st := ScalarFrame.output_contains pre.callee (offset := 32+k) (len := 8) (by omega)
      (a := initial.regValue .rdi + 32 + BitVec.ofNat 64 k + BitVec.ofNat 64 a)
      ⟨a, ha, by simp [BitVec.ofNat_add, BitVec.add_assoc]⟩
    have stk : (Stack.region initial 1168).Contains
        (stackPtr s + BitVec.ofNat 64 l + BitVec.ofNat 64 b).toNat := by
      rw [ScalarFrame.scalar_stack_address (frameOffset := 488) input.rsp (by decide) (by omega : l ≤ 488)]
      exact ScalarFrame.stack_contains pre.callee (offset := 488-l) (len := 8)
        (by omega) (by omega) ⟨b, hb, rfl⟩
    rw [eq] at st
    exact pre.separation _ st stk

end P256.Proofs.Nonce.UpdateValue.Finish
