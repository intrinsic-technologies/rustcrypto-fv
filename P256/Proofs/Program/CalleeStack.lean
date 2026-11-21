import P256.Proofs.Program.Interface
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StackCallLayout (outerReserve inputBytes outputBytes reserve : Nat) where
  stackOffset : Nat
  inputOffset : Nat
  outputOffset : Nat
  aligned : stackOffset % 16 = 0
  capacity : stackOffset + reserve ≤ outerReserve
  inputAbove : inputOffset + 8 ≤ stackOffset
  outputAbove : outputOffset + 8 ≤ stackOffset
  inputEnd : inputBytes ≤ inputOffset + 8
  outputEnd : outputBytes ≤ outputOffset + 8
  separation : outputOffset + inputBytes ≤ inputOffset ∨ inputOffset + outputBytes ≤ outputOffset

variable {inputRegister : Syntax.Reg}

theorem CalleePre.of_stack_region [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {outerReserve inputBytes outputBytes reserve : Nat}
    {childInputRegister : Syntax.Reg}
    (stack : Stack.Valid s outerReserve)
    (avoids : (Stack.region s outerReserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (layout : StackCallLayout outerReserve inputBytes outputBytes reserve)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t) (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t) (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue childInputRegister = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve childInputRegister := by
  rcases layout with ⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩
  dsimp only at rsp input output
  have bounds := stack_bounds stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat - so := by
    rw [rsp]
    exact stack_sub_toNat stack (by omega)
  have hin : (t.regValue childInputRegister).toNat = (stackPtr s).toNat - io := by
    rw [input]
    exact stack_sub_toNat stack (by omega)
  have hout : (t.regValue .rdi).toNat = (stackPtr s).toNat - oo := by
    rw [output]
    exact stack_sub_toNat stack (by omega)
  have hsstart : (Stack.region t reserve).start = (stackPtr s).toNat - (so + reserve) := by
    change (stackPtr t).toNat - reserve = _
    rw [hsp]
    omega
  have hsend : (Stack.region t reserve).start + (Stack.region t reserve).size =
      (stackPtr s).toNat - so + 8 := by
    rw [stack_region_end, hsp]
  have sub (region : MemoryRegion)
      (hstart : (stackPtr s).toNat - outerReserve ≤ region.start)
      (hend : region.start + region.size ≤ (stackPtr s).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region s outerReserve).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (Stack.region s outerReserve).start ≤ a ∧
      a < (Stack.region s outerReserve).start + (Stack.region s outerReserve).size
    rw [stack_region_end]
    change (stackPtr s).toNat - outerReserve ≤ a ∧ a < (stackPtr s).toNat + 8
    constructor <;> omega
  have stackSub := sub (Stack.region t reserve) (by rw [hsstart]; omega) (by rw [hsend]; omega)
  have inputSub := sub (registerRegion t childInputRegister inputBytes)
    (by change _ ≤ (t.regValue childInputRegister).toNat; rw [hin]; omega)
    (by change (t.regValue childInputRegister).toNat + inputBytes ≤ _; rw [hin]; omega)
  have outputSub := sub (registerRegion t .rdi outputBytes)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [hout]; omega)
    (by change (t.regValue .rdi).toNat + outputBytes ≤ _; rw [hout]; omega)
  have allocated (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region s outerReserve).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (stack.2.1 a (hsub a.toNat ha))))
  refine {
    bindingsSupported := supported
    machine := machine
    directionFlag := direction
    loaded := loaded
    rip := rip
    inputBounded := ?_
    inputAllocated := allocated _ inputSub
    outputBounded := ?_
    outputAllocated := allocated _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := outside
    returnInProgram := ret
  }
  · change (t.regValue childInputRegister).toNat + inputBytes < 2^32
    rw [hin]
    omega
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
      have hm : (stackPtr s).toNat % 16 = 8 := stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha hb
      change (t.regValue childInputRegister).toNat ≤ a ∧ a < (t.regValue childInputRegister).toNat + inputBytes at ha
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at hb
      rw [hin] at ha
      rw [hout] at hb
      omega
    · intro a ha hb
      change (t.regValue childInputRegister).toNat ≤ a ∧ a < (t.regValue childInputRegister).toNat + inputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hin] at ha
      rw [hsend] at hb
      omega
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

theorem CalleePre.of_stack [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {outerEntry entry : BitVec 64} {outerInput outerOutput outerReserve inputBytes outputBytes reserve : Nat}
    {childInputRegister : Syntax.Reg}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister)
    (layout : StackCallLayout outerReserve inputBytes outputBytes reserve)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t) (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t) (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue childInputRegister = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve childInputRegister :=
  CalleePre.of_stack_region pre.stack (pre.avoids _ (by simp)) pre.outerBoundary layout
    supported machine direction loaded grow rip rsp input output ret

end P256.Proofs.Program
