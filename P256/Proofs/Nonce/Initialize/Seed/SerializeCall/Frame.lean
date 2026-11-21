import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Pre

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame

theorem serialization_result_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {value : Nat} {orderAddress : BitVec 64} (pre : Nonce.InitializePre s boundary orderAddress)
    (state : Stage s entry boundary 288) (result : Conversions.Int2Octets.Result entry t boundary value)
    (destination : entry.regValue .rdx = stackPtr s - 80) : Stage s t boundary := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 288 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dst : (entry.regValue .rdx).toNat = (stackPtr s).toNat - 80 := by
    rw [destination]
    exact stack_sub_toNat pre.stack (by decide)
  have memory : MemoryWriteFrame entry t #v[registerRegion s .rdi 72, workRegion s 2144] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    apply ha (workRegion s 2144) (by simp)
    have hr' : region = registerRegion entry .rdx 32 ∨ region = Stack.region entry 128 := by
      simpa using hr
    change (stackPtr s).toNat - 2144 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 2144 + 2096
    rcases hr' with rfl | rfl
    · change (entry.regValue .rdx).toNat ≤ a.toNat ∧
        a.toNat < (entry.regValue .rdx).toNat + 32 at hin
      rw [dst] at hin
      constructor <;> omega
    · change (stackPtr entry).toNat - 128 ≤ a.toNat ∧
        a.toNat < (Stack.region entry 128).start + (Stack.region entry 128).size at hin
      rw [stack_region_end] at hin
      change (stackPtr entry).toNat - 128 ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8 at hin
      rw [sp] at hin
      constructor <;> omega
  obtain ⟨n, hn⟩ := state.execution
  obtain ⟨m, hm⟩ := result.execution
  refine ⟨?_, n + m, hn.trans hm⟩
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre.toCalleePre memory), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hr : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hr, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [P256.Proofs.Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre.toCalleePre (by decide) memory bound (by omega)).trans (state.saved e he)
  · have h := output_work_read pre.toCalleePre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Nonce.Initialize.Seed
