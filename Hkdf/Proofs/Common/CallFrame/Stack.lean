import Hkdf.Proofs.Program
import Hkdf.Proofs.Common.CallFrame
import Hkdf.Proofs.Common.Encoding.Serialize.Stack
import Hkdf.Proofs.Common.Machine.Code

set_option autoImplicit false

open Hkdf.Proofs.Program

namespace Hkdf.Proofs.Common.CallFrame

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


open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_sub_toNat {initial : RamState} {reserve offset : Nat}
    (h : Stack.Valid initial reserve) (hoffset : offset ≤ reserve) :
    (stackPtr initial - BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - offset := by
  have hn := h.2.2.1
  have hptr : (stackPtr initial).toNat < 2 ^ 64 := BitVec.isLt _
  have ho : offset < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_trans hoffset hn) hptr
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.le_trans hoffset hn), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine (stack_region_end)

theorem stack_layout_bounds {initial t : RamState}
    {outerReserve inputBytes outputBytes reserve : Nat}
    (outerStack : Stack.Valid initial outerReserve)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset) :
    (registerRegion t .rdi outputBytes).start =
        (stackPtr initial).toNat - layout.outputOffset ∧
    (Stack.region t reserve).start =
        (stackPtr initial).toNat - (layout.stackOffset + reserve) ∧
    (Stack.region t reserve).start + (Stack.region t reserve).size =
        (stackPtr initial).toNat - layout.stackOffset + 8 := by
  have capacity := layout.capacity
  have above := layout.outputAbove
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - layout.stackOffset := by
    rw [rsp]
    exact stack_sub_toNat outerStack (by omega)
  refine ⟨?_, ?_, ?_⟩
  · change (t.regValue .rdi).toNat = _
    rw [output]
    exact stack_sub_toNat outerStack (by omega)
  · change (stackPtr t).toNat - reserve = _
    rw [hsp]
    omega
  · rw [stack_region_end, hsp]

theorem stack_layout_within {initial t : RamState}
    {outerReserve inputBytes outputBytes reserve : Nat}
    (outerStack : Stack.Valid initial outerReserve)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset) :
    ∀ region ∈ #v[registerRegion t .rdi outputBytes, Stack.region t reserve],
      ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a := by
  obtain ⟨hout, hstart, hend⟩ := stack_layout_bounds outerStack layout rsp output
  have capacity := layout.capacity
  have above := layout.outputAbove
  have size := layout.outputEnd
  have low : outerReserve ≤ (stackPtr initial).toNat := outerStack.2.2.1
  intro region hr a ha
  have cases : region = registerRegion t .rdi outputBytes ∨ region = Stack.region t reserve := by
    simpa using hr
  change (Stack.region initial outerReserve).start ≤ a ∧
    a < (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size
  rw [stack_region_end]
  change (stackPtr initial).toNat - outerReserve ≤ a ∧ a < (stackPtr initial).toNat + 8
  rcases cases with rfl | rfl
  · change (registerRegion t .rdi outputBytes).start ≤ a ∧
      a < (registerRegion t .rdi outputBytes).start + outputBytes at ha
    rw [hout] at ha
    constructor <;> omega
  · change (Stack.region t reserve).start ≤ a ∧
      a < (Stack.region t reserve).start + (Stack.region t reserve).size at ha
    rw [hend, hstart] at ha
    constructor <;> omega

theorem stack_layout_disjoint {initial t : RamState}
    {outerReserve inputBytes outputBytes reserve savedOffset savedBytes : Nat}
    (outerStack : Stack.Valid initial outerReserve)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (outputApart : savedOffset + outputBytes ≤ layout.outputOffset ∨
      layout.outputOffset + savedBytes ≤ savedOffset)
    (stackBelow : savedOffset + 8 ≤ layout.stackOffset) :
    ∀ region ∈ #v[registerRegion t .rdi outputBytes, Stack.region t reserve],
      (⟨(stackPtr initial - BitVec.ofNat 64 savedOffset).toNat, savedBytes⟩ : MemoryRegion).Disjoint region := by
  obtain ⟨hout, _, hend⟩ := stack_layout_bounds outerStack layout rsp output
  have capacity := layout.capacity
  have saved := stack_sub_toNat outerStack (offset := savedOffset) (by omega)
  have above := layout.outputAbove
  have low : outerReserve ≤ (stackPtr initial).toNat := outerStack.2.2.1
  intro region hr a ha hb
  have savedLow : (stackPtr initial).toNat - savedOffset ≤ a := by
    have h := ha.1
    change (stackPtr initial - BitVec.ofNat 64 savedOffset).toNat ≤ a at h
    rwa [saved] at h
  have cases : region = registerRegion t .rdi outputBytes ∨ region = Stack.region t reserve := by
    simpa using hr
  rcases cases with rfl | rfl
  · rcases outputApart with outputBelow | outputAbove
    · have high := hb.2
      change a < (registerRegion t .rdi outputBytes).start + outputBytes at high
      rw [hout] at high
      omega
    · have low := hb.1
      change (registerRegion t .rdi outputBytes).start ≤ a at low
      rw [hout] at low
      have high := ha.2
      change a < (stackPtr initial - BitVec.ofNat 64 savedOffset).toNat + savedBytes at high
      rw [saved] at high
      omega
  · have high := hb.2
    change a < (Stack.region t reserve).start + (Stack.region t reserve).size at high
    rw [hend] at high
    omega

theorem callee_pre_of_stack
    [bindings : Bindings] {initial t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {outerReserve inputBytes outputBytes reserve : Nat}
    (stride : UnitStringStride bindings)
    (outerStack : Stack.Valid initial outerReserve)
    (outerAvoid : (Stack.region initial outerReserve).Avoids
      (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (machine : SupportedMachine bindings t)
    (direction : RFLAGS.DirectionFlagClear t.RFLAGS) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  rcases layout with ⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩
  dsimp only at rsp input output
  have bounds : outerReserve ≤ (stackPtr initial).toNat ∧
      (stackPtr initial).toNat + 8 < 2^32 := by
    refine ⟨outerStack.2.2.1, ?_⟩
    have h := outerStack.1
    change (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size < 2^32 at h
    rwa [stack_region_end] at h
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - so := by
    rw [rsp]
    exact stack_sub_toNat outerStack (by omega)
  have hin : (t.regValue .rsi).toNat = (stackPtr initial).toNat - io := by
    rw [input]
    exact stack_sub_toNat outerStack (by omega)
  obtain ⟨hout, hsstart, hsend⟩ := stack_layout_bounds outerStack
    (⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩ :
      Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve) rsp output
  change (registerRegion t .rdi outputBytes).start = (stackPtr initial).toNat - oo at hout
  change (Stack.region t reserve).start = (stackPtr initial).toNat - (so + reserve) at hsstart
  change (Stack.region t reserve).start + (Stack.region t reserve).size =
    (stackPtr initial).toNat - so + 8 at hsend
  have hout' : (t.regValue .rdi).toNat = (stackPtr initial).toNat - oo := hout
  have writableWithin := stack_layout_within outerStack
    (⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩ :
      Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve inputBytes outputBytes reserve) rsp output
  have sub (region : MemoryRegion)
      (hstart : (stackPtr initial).toNat - outerReserve ≤ region.start)
      (hend : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (Stack.region initial outerReserve).start ≤ a ∧
      a < (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size
    rw [stack_region_end]
    change (stackPtr initial).toNat - outerReserve ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have stackSub := writableWithin (Stack.region t reserve) (by simp)
  have inputSub := sub (registerRegion t .rsi inputBytes)
    (by change _ ≤ (t.regValue .rsi).toNat; rw [hin]; omega)
    (by change (t.regValue .rsi).toNat + inputBytes ≤ _; rw [hin]; omega)
  have outputSub := writableWithin (registerRegion t .rdi outputBytes) (by simp)
  have allocated (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region initial outerReserve).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (outerStack.2.1 a (hsub a.toNat ha))))
  refine {
    stride := stride
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
  · change (t.regValue .rsi).toNat + inputBytes < 2^32
    rw [hin]
    omega
  · change (t.regValue .rdi).toNat + outputBytes < 2^32
    rw [hout']
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
      have hm : (stackPtr initial).toNat % 16 = 8 := outerStack.2.2.2
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
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + inputBytes at ha
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at hb
      rw [hin] at ha
      rw [hout'] at hb
      omega
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + inputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hin] at ha
      rw [hsend] at hb
      omega
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hout'] at ha
      rw [hsend] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outerAvoid a (outputSub a.toNat ha)
    · exact outerAvoid a (stackSub a.toNat ha)


theorem callee_pre_of_stack_output
    [bindings : Bindings] {initial t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {outerReserve inputBytes outputBytes reserve : Nat}
    (stride : UnitStringStride bindings)
    (outerStack : Stack.Valid initial outerReserve)
    (outerAvoid : (Stack.region initial outerReserve).Avoids
      (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip)
    (machine : SupportedMachine bindings t)
    (direction : RFLAGS.DirectionFlagClear t.RFLAGS) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout outerReserve 0 outputBytes reserve)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip)
    (inputBounded : (registerRegion t .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion t .rsi inputBytes).Allocated t.external)
    (inputApart : (registerRegion t .rsi inputBytes).Disjoint (Stack.region initial outerReserve)) :
    CalleePre t boundary entry inputBytes outputBytes reserve := by
  obtain ⟨hout, _, hend⟩ := stack_layout_bounds outerStack layout rsp output
  have writableWithin := stack_layout_within outerStack layout rsp output
  have capacity := layout.capacity
  have outputAbove := layout.outputAbove
  have outputEnd := layout.outputEnd
  have stackLow : outerReserve ≤ (stackPtr initial).toNat := outerStack.2.2.1
  have stackHigh : (stackPtr initial).toNat + 8 < 2^32 := by
    have h := outerStack.1
    change (Stack.region initial outerReserve).start + (Stack.region initial outerReserve).size < 2^32 at h
    rwa [stack_region_end] at h
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - layout.stackOffset := by
    rw [rsp]
    exact stack_sub_toNat outerStack (by omega)
  have allocated (region : MemoryRegion)
      (member : region ∈ #v[registerRegion t .rdi outputBytes, Stack.region t reserve]) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (outerStack.2.1 a
        (writableWithin region member a.toNat ha))))
  refine {
    stride := stride
    machine := machine
    directionFlag := direction
    loaded := loaded
    rip := rip
    inputBounded := inputBounded
    inputAllocated := inputAllocated
    outputBounded := ?_
    outputAllocated := allocated _ (by simp)
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := outside
    returnInProgram := ret
  }
  · change (registerRegion t .rdi outputBytes).start + outputBytes < 2^32
    rw [hout]
    omega
  · refine ⟨?_, allocated _ (by simp), ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [hend]
      omega
    · change reserve ≤ (stackPtr t).toNat
      rw [hsp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hsp]
      have aligned := layout.aligned
      have originalAligned : (stackPtr initial).toNat % 16 = 8 := outerStack.2.2.2
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
    · exact fun a ha hb ↦ inputApart a ha
        (writableWithin (registerRegion t .rdi outputBytes) (by simp) a hb)
    · exact fun a ha hb ↦ inputApart a ha
        (writableWithin (Stack.region t reserve) (by simp) a hb)
    · intro a ha hb
      have low : (registerRegion t .rdi outputBytes).start ≤ a := ha.1
      have high : a < (Stack.region t reserve).start + (Stack.region t reserve).size := hb.2
      rw [hout] at low
      rw [hend] at high
      omega
  · intro region hr a ha
    have member : region ∈ #v[registerRegion t .rdi outputBytes, Stack.region t reserve] := by
      simpa using hr
    exact outerAvoid a (writableWithin region member a.toNat ha)

theorem stack_bounds {initial : RamState} {reserve : Nat}
    (stack : Stack.Valid initial reserve) :
    reserve ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 := by
  refine ⟨stack.2.2.1, ?_⟩
  have bound := stack.1
  change (Stack.region initial reserve).start + (Stack.region initial reserve).size < 2^32 at bound
  rwa [stack_region_end] at bound

theorem stack_readable {initial s : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid initial reserve)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (low : offset ≤ reserve) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len := by
  apply Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow (t := s) ?_ grow
  apply Hkdf.Proofs.Common.Machine.memoryRegion_memReadable stack.1 stack.2.1
  · rw [stack_sub_toNat stack low]
    change (stackPtr initial).toNat - reserve ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat stack low]
    have := (stack_bounds stack).1
    omega

theorem stack_writable {initial s : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (low : offset ≤ reserve) (high : len ≤ offset + 8) (positive : 0 < len)
    (_page : (stackPtr initial - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have readable := stack_readable stack grow low high
  refine MemWritable.of_not_reserved positive readable.low readable.mem ?_
  intro i hi reserved
  apply avoid _ ?_ (.inr reserved)
  apply Hkdf.Proofs.Common.Machine.memoryRegion_contains_add stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat stack low]
    change (stackPtr initial).toNat - reserve ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat stack low]
    have := (stack_bounds stack).1
    omega

theorem stack_writable8 {initial s : RamState} {reserve offset : Nat}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (low : offset ≤ reserve) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  apply stack_writable stack avoid grow low (by omega) (by decide)
  rw [stack_sub_toNat stack low]
  have stackalign : (stackPtr initial).toNat % 16 = 8 := stack.2.2.2
  have bounds := stack_bounds stack
  have mod4096 := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - offset)
    (show 8 ∣ 4096 by decide)
  omega

theorem stack_writable4 {initial s : RamState} {reserve offset : Nat}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (low : offset ≤ reserve) (align : offset % 4 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 4 := by
  apply stack_writable stack avoid grow low (by omega) (by decide)
  rw [stack_sub_toNat stack low]
  have stackalign : (stackPtr initial).toNat % 16 = 8 := stack.2.2.2
  have bounds := stack_bounds stack
  have mod4096 := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - offset)
    (show 4 ∣ 4096 by decide)
  omega

theorem stack_writable1 {initial s : RamState} {reserve offset : Nat}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (low : offset ≤ reserve) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 1 := by
  apply stack_writable stack avoid grow low (by omega) (by decide)
  have bound := Nat.mod_lt (stackPtr initial - BitVec.ofNat 64 offset).toNat
    (by decide : 0 < 4096)
  omega

theorem stack_codeApart {initial : RamState} {reserve offset len codeOffset codeLen : Nat}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids InProgram)
    (low : offset ≤ reserve) (high : len ≤ offset + 8)
    (bound : codeOffset + codeLen ≤ 115149) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro j hj k hk eq
  have contains := Hkdf.Proofs.Common.Machine.memoryRegion_contains_add stack.1
    (len := len) (by
      rw [stack_sub_toNat stack low]
      change (stackPtr initial).toNat - reserve ≤ (stackPtr initial).toNat - offset
      omega) (by
      rw [stack_region_end, stack_sub_toNat stack low]
      have := (stack_bounds stack).1
      omega) hj
  apply avoid _ contains
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Hkdf.Proofs.Common.Machine.inProgram_of_textOffset (codeOffset + k) (by omega)

theorem Running.call_stack [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {reserve depth : Nat} {target : RamState → BitVec 64}
    {ret : BitVec 64} {pre : RamState → Prop} {code : CodeMap}
    (run : Running initial boundary #v[Stack.region initial reserve] s)
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 depth)
    (capacity : depth + 8 ≤ reserve) (aligned : (depth + 8) % 8 = 0)
    (off len : Nat) (bound : off + len ≤ 115149)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 off)
    (step : StepEffect pre code (callEffect target ret)) (loaded : CodeIn code s)
    (precondition : PushPre (Extracted.textAddress + BitVec.ofNat 64 off) len s → pre s)
    (continues : target s ≠ boundary.rip) :
    ∃ t, Running initial boundary #v[Stack.region initial reserve] t ∧
      (callEffect target ret s).Holds s t ∧
      returnBoundary t = ⟨ret, stackPtr initial - BitVec.ofNat 64 depth⟩ := by
  have push : pushAddr s = stackPtr initial - BitVec.ofNat 64 (depth + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact stack_writable8 stack avoid run.allocated capacity aligned
  have apart : RangeApart (pushAddr s) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len := by
    rw [push]
    exact stack_codeApart stack (fun a ha hp ↦ avoid a ha (.inl hp)) capacity (by omega) bound
  obtain ⟨t, running, effect, boundaryEq⟩ := run.call step loaded
    (precondition ⟨rip, writable, apart⟩) continues (by
      intro c hc a ha
      simp only [callEffect, pushEffect_components, push, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ha.elim
      · exact ⟨_, Vector.mem_singleton_self _, stackRegion_contains_sub stack.2.2.1
          capacity (by omega : 8 ≤ depth + 8) ha⟩
      · exact ha.elim) (by
        intro r hr a ha hp
        obtain rfl := Vector.mem_singleton.mp hr
        exact avoid a ha (.inl hp))
  exact ⟨t, running, effect, by rwa [rsp] at boundaryEq⟩

end Hkdf.Proofs.Common.CallFrame
