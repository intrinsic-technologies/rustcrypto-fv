import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Memory.Copy
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

variable {v : Variant}

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem allocated_of_memReadable {s : RamState} {address : BitVec 64} {size : Nat}
    (h : MemReadable s address size) :
    (⟨address.toNat, size⟩ : MemoryRegion).Allocated s.external := by
  intro a ha
  have hl : address.toNat ≤ a.toNat := ha.1
  have hh : a.toNat < address.toNat + size := ha.2
  have hi : a.toNat - address.toNat < size := by omega
  have he : address + BitVec.ofNat 64 (a.toNat - address.toNat) = a := by
    have hs : address.toNat + (a.toNat - address.toNat) = a.toNat := by omega
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      congrArg (BitVec.ofNat 64) hs
  exact Option.isSome_iff_exists.mp (he ▸ h.mem _ hi)

theorem allocated_of_grow {initial final : RamState} {small large : MemoryRegion}
    (h : large.Allocated initial.external)
    (hWithin : ∀ a, small.Contains a → large.Contains a)
    (hGrow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (final.external[a]?).isSome) :
    small.Allocated final.external := by
  intro a ha
  obtain ⟨byte, hb⟩ := h a (hWithin a.toNat ha)
  exact Option.isSome_iff_exists.mp (hGrow a (by simp only [hb, Option.isSome_some]))

theorem stack_region_contains_of_bounds {s : RamState} {reserve : Nat} {a : Nat}
    (hLower : (stackPtr s).toNat - reserve ≤ a)
    (hUpper : a < (stackPtr s).toNat + 8) :
    (Stack.region s reserve).Contains a := by
  exact ⟨hLower, by simpa only [stack_region_end] using hUpper⟩

theorem callee_regions [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    {outputBytes outputOffset reserve : Nat} (ctx : Context initial inputs v)
    (rsp : stackPtr s = stackPtr initial - 352)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ 344)
    (stackLow : reserve ≤ 464) :
    (∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
      ∀ a, region.Contains a → (Stack.region initial v.routine.minStackBytes).Contains a) ∧
    (∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      ∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
        ¬ region.Contains a.toNat) := by
  have bounds := validCall_stack_bounds ctx.call
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 352 := by
    rw [rsp]
    exact validCall_stack_sub_toNat ctx.call (by decide)
  have out : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [rdi]
    exact validCall_stack_sub_toNat ctx.call (by omega)
  constructor
  · intro region hr a ha
    have cases : region = registerRegion s .rdi outputBytes ∨
        region = Stack.region s reserve := by simpa using hr
    rcases cases with rfl | rfl
    · change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + outputBytes at ha
      rw [out] at ha
      apply stack_region_contains_of_bounds
      · change (stackPtr initial).toNat - 816 ≤ a
        omega
      · omega
    · have low : (stackPtr s).toNat - reserve ≤ a := ha.1
      have high : a < (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using ha.2
      rw [sp] at low high
      apply stack_region_contains_of_bounds
      · change (stackPtr initial).toNat - 816 ≤ a
        omega
      · omega
  · intro a ha region hr hin
    obtain ⟨i, hi, rfl⟩ := ha
    have base := validCall_stack_sub_toNat ctx.call (offset := 48) (by decide)
    have addr : (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - 48 + i := by
      rw [BitVec.toNat_add]
      change ((stackPtr initial - 48#64).toNat + (BitVec.ofNat 64 i).toNat) % 2^64 = _
      rw [base, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have cases : region = registerRegion s .rdi outputBytes ∨
        region = Stack.region s reserve := by simpa using hr
    rcases cases with rfl | rfl
    · have high := hin.2
      change (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat <
        (s.regValue .rdi).toNat + outputBytes at high
      rw [out, addr] at high
      omega
    · have high : (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat <
          (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using hin.2
      rw [sp, addr] at high
      omega

theorem State.of_callee [bindings : Bindings] {initial s t : RamState}
    {inputs : Array Input} {outputBytes outputOffset reserve : Nat}
    (h : State initial s v) (ctx : Context initial inputs v)
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - 352)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ 344)
    (stackLow : reserve ≤ 464) : State initial t v := by
  obtain ⟨n, hn⟩ := h.execution
  obtain ⟨m, hm⟩ := result.execution
  obtain ⟨within, avoids⟩ := callee_regions ctx rsp rdi outputHigh outputLow stackLow
  refine ⟨⟨n + m, hn.trans hm⟩, result.machine, result.loaded,
    fun a ha => result.allocated a (h.allocated a ha),
    h.saved.of_bytes (fun a ha => result.frame a (avoids a ha)),
    result.abi.2.1,
    ?_⟩
  apply memoryWriteFrame_trans h.frame
  intro address outside
  exact result.frame address (fun region hr ha => outside _ (by simp)
    (within region hr address.toNat ha))

theorem call [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    (offset : Nat) (displacement : BitVec 32)
    (size : offset + 5 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 displacement)
    (target : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)).toNat < 2^32)
    (targetProgram : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)))
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - 344) :
    ∃ t, State initial t v ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (displacement.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) s).Holds s t ∧
      stackPtr t = stackPtr initial - 352 ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 := by
  have address : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    have hw := validCall_stack_sub_writable8 ctx.call (offset := 352) (by decide) (by decide)
    exact ⟨hw.low, fun i hi => state.allocated _ (hw.mem i hi), hw.tables⟩
  have instruction := programText_slice (programLoaded_codeIn state.loaded) offset
    (encodeCallRel32 displacement) size bytes
  have separate : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) 5 := by
    rw [address]
    exact stack_codeApart ctx (by decide) (by decide) size
  obtain ⟨t, run, ready, effect⟩ :=
    (call_rel32_effect_step _ displacement target).advances
      (supportedMachine_readyToStep state.machine) instruction ⟨rip, writable, separate⟩
      (boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 targetProgram)
  have frame : AgreesExcept [.reg 4, .mem (stackPtr initial - 352) 8, .rip] s t := by
    simpa only [callEffect, pushEffect_components, address] using effect.agrees
  have writes : WritesWithin [.reg 4, .mem (stackPtr initial - 352) 8, .rip]
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨Stack.region initial v.routine.minStackBytes, by simp,
        stackRegion_contains_sub ctx.call.stack.2.2.1 (by change 352 ≤ 816; decide) (by decide) ha⟩
    · exact ha.elim
  have saved : ∀ c ∈ [Component.reg 4, .mem (stackPtr initial - 352) 8, .rip], ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact id
    · obtain ⟨i, hi, rfl⟩ := ha
      rintro ⟨j, hj, he⟩
      apply OffsetsApart.ne (c₁ := -352) (len₁ := 8) (c₂ := -48) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · exact id
  refine ⟨t, state.of_agrees ctx run ready frame writes saved, effect,
    effect.writes.1.trans address, (callEffect_stack effect).1⟩

theorem call_m64 [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    (offset : Nat) (displacement : BitVec 32) (callee : BitVec 64)
    (size : offset + 6 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip displacement))
    (target : callee.toNat < 2^32) (targetProgram : InProgram callee)
    (readable : MemReadable s
      ((AddrMode.rip displacement).addr s (Extracted.textAddress + BitVec.ofNat 64 offset + 6)) 8)
    (pointer : callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip displacement) s = callee)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - 344) :
    ∃ t, State initial t v ∧
      (callEffect (fun _ => callee)
        (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t ∧
      stackPtr t = stackPtr initial - 352 ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 6 := by
  have address : pushAddr s = stackPtr initial - 352 := by
    rw [pushAddr, rsp, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    have hw := validCall_stack_sub_writable8 ctx.call (offset := 352) (by decide) (by decide)
    exact ⟨hw.low, fun i hi => state.allocated _ (hw.mem i hi), hw.tables⟩
  have instruction := programText_slice (programLoaded_codeIn state.loaded) offset
    (encodeCallM64 (.rip displacement)) size bytes
  have separate : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) 6 := by
    rw [address]
    exact stack_codeApart ctx (by decide) (by decide) size
  obtain ⟨t, run, ready, indirectEffect⟩ :=
    (call_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset)
      (.rip displacement) trivial rfl rfl).advances
      (supportedMachine_readyToStep state.machine) instruction
      ⟨⟨⟨rip, writable, separate⟩, by rw [pointer]; exact target⟩, readable⟩
      (by change callMemPtr _ _ s ≠ (returnBoundary initial).rip
          rw [pointer]
          exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 targetProgram)
  change (callEffect (callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip displacement))
    (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t at indirectEffect
  have effect : (callEffect (fun _ => callee)
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t := by
    simpa only [callEffect, pushEffect, pointer] using indirectEffect
  have frame : AgreesExcept [.reg 4, .mem (stackPtr initial - 352) 8, .rip] s t := by
    simpa only [callEffect, pushEffect_components, address] using effect.agrees
  have writes : WritesWithin [.reg 4, .mem (stackPtr initial - 352) 8, .rip]
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨Stack.region initial v.routine.minStackBytes, by simp,
        stackRegion_contains_sub ctx.call.stack.2.2.1 (by change 352 ≤ 816; decide) (by decide) ha⟩
    · exact ha.elim
  have saved : ∀ c ∈ [Component.reg 4, .mem (stackPtr initial - 352) 8, .rip], ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact id
    · obtain ⟨i, hi, rfl⟩ := ha
      rintro ⟨j, hj, he⟩
      apply OffsetsApart.ne (c₁ := -352) (len₁ := 8) (c₂ := -48) (len₂ := 56)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · exact id
  refine ⟨t, state.of_agrees ctx run ready frame writes saved, effect,
    effect.writes.1.trans address, (callEffect_stack effect).1⟩

theorem callee_pre [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    {entry : BitVec 64} {inputBytes outputBytes outputOffset reserve : Nat}
    (ctx : Context initial inputs v) (state : State initial s v)
    (rip : s.RIP = entry) (rsp : stackPtr s = stackPtr initial - 352)
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ 344)
    (reserveBound : reserve ≤ 464)
    (inputBounded : (registerRegion s .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion s .rsi inputBytes).Allocated s.external)
    (inputApart : (registerRegion s .rsi inputBytes).Disjoint (Stack.region initial v.routine.minStackBytes))
    (_ret : InProgram (returnBoundary s).rip) :
    CalleePre s (returnBoundary initial) entry inputBytes outputBytes reserve := by
  have within := (callee_regions (outputBytes := outputBytes) (outputOffset := outputOffset) (reserve := reserve)
    ctx rsp rdi outputHigh outputLow reserveBound).1
  have outputWithin := within (registerRegion s .rdi outputBytes) (by simp)
  have stackWithin := within (Stack.region s reserve) (by simp)
  have bounds := validCall_stack_bounds ctx.call
  have spNat : (stackPtr s).toNat = (stackPtr initial).toNat - 352 := by
    rw [rsp]
    exact validCall_stack_sub_toNat ctx.call (by decide)
  have outNat : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [rdi]
    exact validCall_stack_sub_toNat ctx.call (by omega)
  refine {
    stride := ctx.stride
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := inputBounded
    inputAllocated := inputAllocated
    outputBounded := ?_
    outputAllocated := allocated_of_grow ctx.call.stack.2.1 outputWithin state.allocated
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := (validCall_returnBoundary ctx.machine ctx.call).2.2
  }
  · change (s.regValue .rdi).toNat + outputBytes < 2^32
    rw [outNat]
    omega
  · refine ⟨?_, allocated_of_grow ctx.call.stack.2.1 stackWithin state.allocated, ?_, ?_⟩
    · change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32
      rw [stack_region_end, spNat]
      omega
    · change reserve ≤ (stackPtr s).toNat
      rw [spNat]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [spNat]
      have align : (stackPtr initial).toNat % 16 = 8 := ctx.call.stack.2.2.2
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
    · change (registerRegion s .rsi inputBytes).Disjoint (registerRegion s .rdi outputBytes)
      exact fun a ha hb => inputApart a ha (outputWithin a hb)
    · change (registerRegion s .rsi inputBytes).Disjoint (Stack.region s reserve)
      exact fun a ha hb => inputApart a ha (stackWithin a hb)
    · change (registerRegion s .rdi outputBytes).Disjoint (Stack.region s reserve)
      intro a ha hb
      have low : (s.regValue .rdi).toNat ≤ a := ha.1
      have high : a < (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using hb.2
      rw [outNat] at low
      rw [spNat] at high
      omega
  · intro region hr address ha
    apply (ctx.call.separation.2 (Stack.region initial v.routine.minStackBytes) (by simp)).2 address
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outputWithin address.toNat ha
    · exact stackWithin address.toNat ha

theorem rodata_loaded {s : RamState} (loaded : ProgramLoaded s) {offset : Nat}
    (bound : offset < 680) :
    s.external[Extracted.rodataAddress + BitVec.ofNat 64 offset]? =
      some (Extracted.rodataBytes.toList[offset]'(by
        simpa only [chunked_toList_length, rodataBytes_size] using bound)) := by
  apply loaded
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.rodataAddress, Extracted.rodataBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ _ _

theorem memset_pointer {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x200288 8 ∧ (Operand.mem 0x200288 : Operand 64).read s = 0x10dd10 := by
  have bytes : ∀ i : Fin 8,
      Extracted.rodataBytes.toList[648 + i.val]'(by
        rw [chunked_toList_length, rodataBytes_size]
        omega) = storedByte (0x10dd10 : BitVec 64) i.val := by decide +kernel
  have stored : Bytes s.external 0x200288 8 (storedByte (0x10dd10 : BitVec 64)) := by
    intro i hi
    have byte := rodata_loaded loaded (offset := 648 + i) (by omega)
    rw [bytes ⟨i, hi⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  exact ⟨stored.readable (by decide), stored.memLoad (by decide) (by decide)⟩

theorem memcpy_pointer {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x200280 8 ∧ (Operand.mem 0x200280 : Operand 64).read s = 0x10dd60 := by
  have bytes : ∀ i : Fin 8,
      Extracted.rodataBytes.toList[640 + i.val]'(by
        rw [chunked_toList_length, rodataBytes_size]
        omega) = storedByte (0x10dd60 : BitVec 64) i.val := by decide +kernel
  have stored : Bytes s.external 0x200280 8 (storedByte (0x10dd60 : BitVec 64)) := by
    intro i hi
    have byte := rodata_loaded loaded (offset := 640 + i) (by omega)
    rw [bytes ⟨i, hi⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  exact ⟨stored.readable (by decide), stored.memLoad (by decide) (by decide)⟩

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

section

variable [bindings : Bindings] {initial t : RamState} {inputs : Array Input}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}
    (hBindings : UnitStringStride bindings) (hMachine : SupportedMachine bindings initial)
    (hCall : ValidCall v.routine initial inputs)
    (machine : SupportedMachine bindings t) (direction : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS)
    (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)

include hBindings hMachine hCall machine direction loaded grow

theorem callee_pre_of_stack
    (layout : StackCallLayout 816 inputBytes outputBytes reserve)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (_ret : InProgram (returnBoundary t).rip) :
    CalleePre t (returnBoundary initial) entry inputBytes outputBytes reserve := by
  rcases layout with ⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩
  dsimp only at rsp input output
  have bounds := validCall_stack_bounds hCall
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - so := by
    rw [rsp]
    exact validCall_stack_sub_toNat hCall (by omega)
  have hin : (t.regValue .rsi).toNat = (stackPtr initial).toNat - io := by
    rw [input]
    exact validCall_stack_sub_toNat hCall (by omega)
  have hout : (t.regValue .rdi).toNat = (stackPtr initial).toNat - oo := by
    rw [output]
    exact validCall_stack_sub_toNat hCall (by omega)
  have hsstart : (Stack.region t reserve).start = (stackPtr initial).toNat - (so + reserve) := by
    change (stackPtr t).toNat - reserve = _
    rw [hsp]
    omega
  have hsend : (Stack.region t reserve).start + (Stack.region t reserve).size =
      (stackPtr initial).toNat - so + 8 := by
    rw [stack_region_end, hsp]
  have sub (region : MemoryRegion)
      (hstart : (stackPtr initial).toNat - 816 ≤ region.start)
      (hend : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial 816).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (Stack.region initial 816).start ≤ a ∧
      a < (Stack.region initial 816).start + (Stack.region initial 816).size
    rw [stack_region_end]
    change (stackPtr initial).toNat - 816 ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have stackSub := sub (Stack.region t reserve) (by rw [hsstart]; omega) (by rw [hsend]; omega)
  have inputSub := sub (registerRegion t .rsi inputBytes)
    (by change _ ≤ (t.regValue .rsi).toNat; rw [hin]; omega)
    (by change (t.regValue .rsi).toNat + inputBytes ≤ _; rw [hin]; omega)
  have outputSub := sub (registerRegion t .rdi outputBytes)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [hout]; omega)
    (by change (t.regValue .rdi).toNat + outputBytes ≤ _; rw [hout]; omega)
  have allocated (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region initial 816).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (hCall.stack.2.1 a (hsub a.toNat ha))))
  refine {
    stride := hBindings
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
    outerBoundary := (validCall_returnBoundary hMachine hCall).2.2
  }
  · change (t.regValue .rsi).toNat + inputBytes < 2^32
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
      have hm : (stackPtr initial).toNat % 16 = 8 := hCall.stack.2.2.2
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
      rw [hout] at hb
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
      rw [hout] at ha
      rw [hsend] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hCall.separation.2 _ (by change _ ∈ [outputRegion v.routine initial, Stack.region initial 816]; simp)).2 a (outputSub a.toNat ha)
    · exact (hCall.separation.2 _ (by change _ ∈ [outputRegion v.routine initial, Stack.region initial 816]; simp)).2 a (stackSub a.toNat ha)

end

end Sha2.Proofs.Wrapper
