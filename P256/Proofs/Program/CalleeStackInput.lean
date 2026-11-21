import P256.Proofs.Program.Interface
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StackBufferLayout (outerReserve bufferBytes reserve : Nat) where
  stackOffset : Nat
  bufferOffset : Nat
  aligned : stackOffset % 16 = 0
  capacity : stackOffset + reserve ≤ outerReserve
  bufferAbove : bufferOffset + 8 ≤ stackOffset
  bufferEnd : bufferBytes ≤ bufferOffset + 8

variable {inputRegister : Syntax.Reg}

theorem CalleePre.of_disjoint_input_and_stack [bindings : Bindings]
    {initial t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64}
    {outerReserve inputBytes outputBytes reserve : Nat}
    (layout : StackBufferLayout outerReserve outputBytes reserve)
    (stack : Stack.Valid initial outerReserve)
    (avoids : (Stack.region initial outerReserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (hBindings : MachineRamUnitStrideDecodable bindings t)
    (hMachine : SupportedIntegerMachineState bindings.processor t)
    (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS) (loaded : ProgramLoaded t)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (inputBounded : (registerRegion t .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion t .rsi inputBytes).Allocated t.external)
    (inputDisjoint : (registerRegion t .rsi inputBytes).Disjoint (Stack.region initial outerReserve))
    (destination : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.bufferOffset)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (outer : ¬ InProgram boundary.rip) (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  rcases layout with ⟨so, oo, align, capacity, bufferAbove, bufferEnd⟩
  dsimp only at rsp destination
  have bounds := stack_bounds stack
  have sp : (stackPtr t).toNat = (stackPtr initial).toNat - so := by
    rw [rsp]
    exact stack_sub_toNat stack (by omega)
  have dst : (t.regValue .rdi).toNat = (stackPtr initial).toNat - oo := by
    rw [destination]
    exact stack_sub_toNat stack (by omega)
  have stackStart : (Stack.region t reserve).start = (stackPtr initial).toNat - (so + reserve) := by
    change (stackPtr t).toNat - reserve = _
    rw [sp]
    omega
  have stackEnd : (Stack.region t reserve).start + (Stack.region t reserve).size =
      (stackPtr initial).toNat - so + 8 := by
    rw [stack_region_end]
    change (stackPtr t).toNat + 8 = _
    rw [sp]
  have sub (region : MemoryRegion)
      (lo : (stackPtr initial).toNat - outerReserve ≤ region.start)
      (hi : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (stackPtr initial).toNat - outerReserve ≤ a ∧
      a < (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size
    rw [stack_region_end]
    constructor <;> omega
  have stackSub := sub (Stack.region t reserve) (by rw [stackStart]; omega)
    (by rw [stackEnd]; omega)
  have outputSub := sub (registerRegion t .rdi outputBytes)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [dst]; omega)
    (by change (t.regValue .rdi).toNat + outputBytes ≤ _; rw [dst]; omega)
  have allocated (region : MemoryRegion)
      (hs : ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (stack.2.1 a (hs a.toNat ha))))
  refine ⟨hBindings, hMachine, direction, loaded, rip, inputBounded, inputAllocated,
    ?_, allocated _ outputSub, ?_, ?_, ?_, outer, ret⟩
  · change (t.regValue .rdi).toNat + outputBytes < 2^32
    rw [dst]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [stackEnd]
      omega
    · change reserve ≤ (stackPtr t).toNat
      rw [sp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [sp]
      have hm : (stackPtr initial).toNat % 16 = 8 := stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by change i.val < j.val at hij; omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha hb
      exact inputDisjoint a ha (outputSub a hb)
    · intro a ha hb
      exact inputDisjoint a ha (stackSub a hb)
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [dst] at ha
      rw [stackEnd] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact avoids a (outputSub a.toNat ha)
    · exact avoids a (stackSub a.toNat ha)

theorem CalleePre.of_input_and_stack [bindings : Bindings]
    {s t : RamState} {boundary : ReturnBoundary} {outerEntry entry : BitVec 64}
    {inputBytes outerOutput outerReserve outputBytes reserve : Nat}
    (pre : CalleePre s boundary outerEntry inputBytes outerOutput outerReserve inputRegister)
    (layout : StackBufferLayout outerReserve outputBytes reserve)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t)
    (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = s.regValue inputRegister)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.bufferOffset)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  have he : registerRegion t .rsi inputBytes = registerRegion s inputRegister inputBytes := by
    simp only [registerRegion, input]
  apply CalleePre.of_disjoint_input_and_stack layout pre.stack
    (pre.avoids _ (by simp)) supported machine direction loaded rip rsp
    (he.symm ▸ pre.inputBounded) _ _ output grow pre.outerBoundary ret
  · rw [he]
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))
  · rw [he]
    exact pre.separation 0 2 (by decide)

end P256.Proofs.Program
