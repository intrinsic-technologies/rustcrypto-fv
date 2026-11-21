import Sha2.Proofs.Common.Machine.StackCall

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
open X86.UserProcess X86Proofs

theorem callee_pre_of_input [bindings : Bindings] {initial t : RamState}
    {entry : BitVec 64} {outerReserve inputBytes outputBytes reserve : Nat}
    (stride : UnitStringStride bindings) (initialMachine : SupportedMachine bindings initial)
    (stack : Stack.Valid initial outerReserve)
    (avoids : (Stack.region initial outerReserve).Avoids
      (fun a => InProgram a ∨ InPageTables a))
    (returnAddress : ValidReturnAddress initial)
    (machine : SupportedMachine bindings t) (direction : RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (stackOffset outputOffset : Nat)
    (aligned : stackOffset % 16 = 0) (capacity : stackOffset + reserve ≤ outerReserve)
    (outputAbove : outputOffset + 8 ≤ stackOffset) (outputEnd : outputBytes ≤ outputOffset + 8)
    (inputBounded : (registerRegion t .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion t .rsi inputBytes).Allocated t.external)
    (inputApart : (registerRegion t .rsi inputBytes).Disjoint (Stack.region initial outerReserve))
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 stackOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (_ret : InProgram (returnBoundary t).rip) :
    CalleePre t (returnBoundary initial) entry inputBytes outputBytes reserve := by
  have bounds := stack_valid_bounds stack
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - stackOffset := by
    rw [rsp]
    exact stack_valid_sub_toNat stack (by omega)
  have hout : (t.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [output]
    exact stack_valid_sub_toNat stack (by omega)
  have hsstart : (Stack.region t reserve).start =
      (stackPtr initial).toNat - (stackOffset + reserve) := by
    change (stackPtr t).toNat - reserve = _
    rw [hsp]
    omega
  have hsend : (Stack.region t reserve).start + (Stack.region t reserve).size =
      (stackPtr initial).toNat - stackOffset + 8 := by
    rw [stack_region_end, hsp]
  have sub (region : MemoryRegion)
      (lower : (stackPtr initial).toNat - outerReserve ≤ region.start)
      (upper : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (Stack.region initial outerReserve).start ≤ a ∧
      a < (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size
    rw [stack_region_end]
    change (stackPtr initial).toNat - outerReserve ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have stackSub := sub (Stack.region t reserve)
    (by rw [hsstart]; omega) (by rw [hsend]; omega)
  have outputSub := sub (registerRegion t .rdi outputBytes)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [hout]; omega)
    (by change (t.regValue .rdi).toNat + outputBytes ≤ _; rw [hout]; omega)
  have allocated (region : MemoryRegion)
      (contained : ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (stack.2.1 a (contained a.toNat ha))))
  refine {
    stride := stride
    machine := machine
    directionFlag := direction
    loaded := loaded
    rip := rip
    inputBounded := inputBounded
    inputAllocated := inputAllocated
    outputBounded := ?_
    outputAllocated := allocated _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := (valid_return_boundary initialMachine stack returnAddress).2.2
  }
  · change (t.regValue .rdi).toNat + outputBytes < 2^32
    rw [hout]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [hsend]
      omega
    · change reserve ≤ (stackPtr t).toNat
      rw [hsp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hsp]
      have original : (stackPtr initial).toNat % 16 = 8 := stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha hb
      exact inputApart a ha (outputSub a hb)
    · intro a ha hb
      exact inputApart a ha (stackSub a hb)
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hout] at ha
      rw [hsend] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact avoids a (outputSub a.toNat ha)
    · exact avoids a (stackSub a.toNat ha)

end Sha2.Proofs.Common.Machine
