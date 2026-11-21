import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem StackCallLayout.regions_within {s t : RamState}
    {outerReserve inputBytes outputBytes reserve : Nat}
    (layout : StackCallLayout outerReserve inputBytes outputBytes reserve)
    (stack : Stack.Valid s outerReserve)
    (rsp : stackPtr t = stackPtr s-BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr s-BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s-BitVec.ofNat 64 layout.outputOffset) :
    ∀ region ∈ [registerRegion t .rsi inputBytes,registerRegion t .rdi outputBytes,
      Stack.region t reserve], ∀ a, region.Contains a → (Stack.region s outerReserve).Contains a := by
  have bounds := stack_bounds stack
  have reader : (t.regValue .rsi).toNat = (stackPtr s).toNat-layout.inputOffset := by
    rw [input]; exact stack_sub_toNat stack (by have := layout.inputAbove; have := layout.capacity; omega)
  have result : (t.regValue .rdi).toNat = (stackPtr s).toNat-layout.outputOffset := by
    rw [output]; exact stack_sub_toNat stack (by have := layout.outputAbove; have := layout.capacity; omega)
  have sp : (stackPtr t).toNat = (stackPtr s).toNat-layout.stackOffset := by
    rw [rsp]; exact stack_sub_toNat stack (by have := layout.capacity; omega)
  have inputAbove := layout.inputAbove
  have outputAbove := layout.outputAbove
  have inputEnd := layout.inputEnd
  have outputEnd := layout.outputEnd
  have capacity := layout.capacity
  intro region hr a ha
  change (stackPtr s).toNat-outerReserve ≤ a ∧ a < (Stack.region s outerReserve).start+(Stack.region s outerReserve).size
  rw [stack_region_end]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat+inputBytes at ha
    rw [reader] at ha
    constructor <;> omega
  · change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+outputBytes at ha
    rw [result] at ha
    constructor <;> omega
  · change (stackPtr t).toNat-reserve ≤ a ∧ a < (Stack.region t reserve).start+(Stack.region t reserve).size at ha
    rw [stack_region_end,sp] at ha
    constructor <;> omega

end P256.Proofs.Program
