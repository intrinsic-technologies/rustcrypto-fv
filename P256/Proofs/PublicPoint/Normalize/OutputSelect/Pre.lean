import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Stack
import P256.Proofs.Field.Stack
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.OutputSelect

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {inputRegister : Syntax.Reg}

theorem output_address [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve offset len : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (bound : offset + len ≤ outputBytes) :
    (s.regValue .rdi + BitVec.ofNat 64 offset).toNat = (s.regValue .rdi).toNat + offset := by
  have hb : (s.regValue .rdi).toNat + outputBytes < 2^32 := pre.outputBounded
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

theorem output_sub [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve offset len : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (output : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 offset)
    (bound : offset + len ≤ outputBytes) :
    ∀ a, (registerRegion t .rdi len).Contains a → (registerRegion s .rdi outputBytes).Contains a := by
  intro a ha
  have hn : (t.regValue .rdi).toNat = (s.regValue .rdi).toNat + offset := by
    rw [output]; exact output_address pre bound
  change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + len at ha
  change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + outputBytes
  rw [hn] at ha
  constructor <;> omega

theorem callee_pre [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {outerEntry entry : BitVec 64} {outerInput outerOutput outerReserve inputBytes outputBytes reserve outputOffset : Nat}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister)
    (layout : StackBufferLayout outerReserve inputBytes reserve)
    (supported : MachineRamUnitStrideDecodable bindings t)
    (machine : SupportedIntegerMachineState bindings.processor t) (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t) (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = entry) (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.bufferOffset)
    (output : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 outputOffset)
    (outputBound : outputOffset + outputBytes ≤ outerOutput)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  have outBound : (s.regValue .rdi).toNat + outerOutput < 2^32 := pre.outputBounded
  have outNat : (t.regValue .rdi).toNat = (s.regValue .rdi).toNat + outputOffset := by
    rw [output, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : outputOffset < 2^64), Nat.mod_eq_of_lt (by omega)]
  have outputSub : ∀ a, (registerRegion t .rdi outputBytes).Contains a →
      (registerRegion s .rdi outerOutput).Contains a := by
    intro a ha
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at ha
    change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + outerOutput
    rw [outNat] at ha
    constructor <;> omega
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
    outputBounded := by
      change (t.regValue .rdi).toNat + outputBytes < 2^32
      rw [outNat]; omega
    outputAllocated := by
      intro a ha
      exact Option.isSome_iff_exists.mp (grow a
        (Option.isSome_iff_exists.mpr (pre.outputAllocated a (outputSub a.toNat ha))))
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
      · change (registerRegion s .rdi outerOutput).Contains a
        change (registerRegion t .rdi outputBytes).Contains a at hb
        exact outputSub a hb
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
      · change (registerRegion s .rdi outerOutput).Contains a
        change (registerRegion t .rdi outputBytes).Contains a at ha
        exact outputSub a ha
      · exact stackSub a hb
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply pre.avoids (registerRegion s .rdi outerOutput) (by simp) a
      exact outputSub a.toNat ha
    · exact pre.avoids _ (by simp) a (stackSub a.toNat ha)

theorem binary_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {leftOffset rightOffset outputOffset : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : ScalarFrame.FrameState s t 65 3352 1952)
    (leftAbove : leftOffset ≤ 1944) (leftEnd : 24 ≤ leftOffset)
    (rightAbove : rightOffset ≤ 1944) (rightEnd : 24 ≤ rightOffset)
    (outputBound : outputOffset + 32 ≤ 65)
    (rip : t.RIP = 0x114380)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 leftOffset)
    (right : t.regValue .rdx = stackPtr s - BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 outputOffset)
    (ret : InProgram (returnBoundary t).rip) : Field.BinaryFieldPre t boundary 0x114380 128 := by
  have bounds := stack_bounds pre.stack
  have hr : (t.regValue .rdx).toNat = (stackPtr s).toNat - rightOffset := by
    rw [right]; exact stack_sub_toNat pre.stack (by omega)
  have hs : (stackPtr t).toNat = (stackPtr s).toNat - 1952 := by
    rw [state.rsp]; exact stack_sub_toNat pre.stack (by decide)
  have rightSub : ∀ a, (registerRegion t .rdx 32).Contains a → (Stack.region s 3352).Contains a := by
    intro a ha
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    rw [hr] at ha
    change (stackPtr s).toNat - 3352 ≤ a ∧ a < (Stack.region s 3352).start + (Stack.region s 3352).size
    rw [stack_region_end]
    constructor <;> omega
  refine {
    toCalleePre := callee_pre pre
      (⟨1952,leftOffset,by decide,by decide,by omega,by omega⟩ : StackBufferLayout 3352 32 128)
      state.bindingsSupported state.machine state.directionFlag state.loaded state.allocated
      rip state.rsp input output outputBound ret
    rightBounded := ?_, rightAllocated := ?_, rightOutput := ?_, rightStack := ?_ }
  · change (t.regValue .rdx).toNat + 32 < 2^32
    rw [hr]; omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (rightSub a.toNat ha))))
  · intro a ha hb
    exact pre.separation 1 2 (by decide) a (output_sub pre output outputBound a hb) (rightSub a ha)
  · intro a ha hb
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    change (Stack.region t 128).start ≤ a ∧ a < (Stack.region t 128).start + (Stack.region t 128).size at hb
    rw [hr] at ha
    rw [stack_region_end, hs] at hb
    omega

end P256.Proofs.PublicPoint.Normalize.OutputSelect
