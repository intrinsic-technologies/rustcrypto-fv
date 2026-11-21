import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {inputRegister : Syntax.Reg}

theorem CalleePre.of_stack_and_output [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {outerEntry entry : BitVec 64} {outerInput outerReserve inputBytes outputBytes reserve : Nat}
    (pre : CalleePre s boundary outerEntry outerInput outputBytes outerReserve inputRegister)
    (layout : StackBufferLayout outerReserve inputBytes reserve)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t) (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t) (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.bufferOffset)
    (output : t.regValue .rdi = s.regValue .rdi)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  rcases layout with ⟨so, io, align, capacity, inputAbove, inputEnd⟩
  dsimp only at rsp input output
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat - so := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by omega)
  have hin : (t.regValue .rsi).toNat = (stackPtr s).toNat - io := by
    rw [input]
    exact stack_sub_toNat pre.stack (by omega)
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
  have inputSub := sub (registerRegion t .rsi inputBytes)
    (by change _ ≤ (t.regValue .rsi).toNat; rw [hin]; omega)
    (by change (t.regValue .rsi).toNat + inputBytes ≤ _; rw [hin]; omega)
  have allocated (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region s outerReserve).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (hsub a.toNat ha))))
  refine {
    bindingsSupported := supported
    machine := machine
    directionFlag := direction
    loaded := loaded
    rip := rip
    inputBounded := ?_
    inputAllocated := allocated _ inputSub
    outputBounded := by simpa only [registerRegion, output] using pre.outputBounded
    outputAllocated := by
      change (MemoryRegion.mk (t.regValue .rdi).toNat outputBytes).Allocated t.external
      rw [output]
      intro a ha
      exact Option.isSome_iff_exists.mp (grow a
        (Option.isSome_iff_exists.mpr (pre.outputAllocated a ha)))
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := pre.outerBoundary
    returnInProgram := ret
  }
  · change (t.regValue .rsi).toNat + inputBytes < 2^32
    rw [hin]
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
      have hm : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
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
      apply pre.separation 1 2 (by decide) a
      · change (registerRegion s .rdi outputBytes).Contains a
        change (registerRegion t .rdi outputBytes).Contains a at hb
        simpa only [registerRegion, output] using hb
      · exact inputSub a ha
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + inputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hin] at ha
      rw [hsend] at hb
      omega
    · intro a ha hb
      apply pre.separation 1 2 (by decide) a
      · change (registerRegion s .rdi outputBytes).Contains a
        change (registerRegion t .rdi outputBytes).Contains a at ha
        simpa only [registerRegion, output] using ha
      · exact stackSub a hb
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply pre.avoids (registerRegion s .rdi outputBytes) (by simp) a
      simpa only [registerRegion, output] using ha
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

end P256.Proofs.Program
