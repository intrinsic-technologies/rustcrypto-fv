import K256.Proofs.ParseSignature.Wrapper.Frame
import K256.Proofs.Common.SignatureBuffers

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Spec.Program K256.Proofs.Common Prelude X86 X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine

private theorem stackSubToNat {sp : BitVec 64} {offset : Nat} (h : offset ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 offset).toNat = sp.toNat - offset := by
  have ho : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h sp.isLt)]
  rw [BitVec.toNat_sub_of_le (by rwa [BitVec.le_def, ho]), ho]

private theorem stackRegionEnd (s : RamState) (len : Nat) :
    (Stack.region s len).start + (Stack.region s len).size = (s.regValue .rsp).toNat + 8 := by
  change (s.regValue .rsp).toNat - len +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - len)) = _
  omega

private theorem stackBounds {initial : RamState}
    (stack : Stack.Valid initial signatureFromSlice.minStackBytes) :
    784 ≤ (initial.regValue .rsp).toNat ∧ (initial.regValue .rsp).toNat + 8 < 2 ^ 32 := by
  refine ⟨stack.2.2.1, ?_⟩
  have low := stack.1
  unfold MemoryRegion.Bounded at low
  rwa [stackRegionEnd] at low

private theorem pairPushFrame {initial : RamState}
    (stack : Stack.Valid initial signatureFromSlice.minStackBytes) :
    RamWriteFrame initial.external (pairFrame initial).original
      [Stack.region initial signatureFromSlice.minStackBytes] := by
  let sp := initial.regValue .rsp
  obtain ⟨room, low⟩ : 784 ≤ sp.toNat ∧ sp.toNat + 8 < 2 ^ 32 := stackBounds stack
  have within (off : Nat) (bound : off ≤ 784) :
      InRegions [Stack.region initial signatureFromSlice.minStackBytes]
        (sp - BitVec.ofNat 64 off) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    unfold InRegion
    rw [stackSubToNat (by omega : off ≤ sp.toNat), stackRegionEnd]
    change sp.toNat - 784 ≤ _ ∧ _ + 8 ≤ sp.toNat + 8 ∧ _ + 8 ≤ 2 ^ 64
    omega
  exact ((RamWriteFrame.refl _ _).memStore (initial.regValue .rbx)
    (within 8 (by decide))).memStore
      (0x102468 : BitVec 64) (within 96 (by decide))

theorem pairBuffers {initial : RamState} {bytes : ByteArray}
    (call : ValidCall signatureFromSlice initial [bytes]) (size : bytes.size = 64) :
    let fr := pairFrame initial
    Readable fr.original fr.rsi 64 ∧ Writable Extracted.programImage fr.original fr.rdi 72 ∧
      Outside [callStack fr] fr.rsi 64 ∧ Outside [callStack fr] fr.rdi 72 ∧
      ∀ j < 8, memLoad fr.original (wordAddr fr.rsi 64 j) 64 =
        memLoad initial.external (wordAddr fr.rsi 64 j) 64 := by
  intro fr
  let sp := initial.regValue .rsp
  let stack := Stack.region initial signatureFromSlice.minStackBytes
  have room : 784 ≤ sp.toNat := call.stackAvailable.2.2.1
  obtain ⟨input, _, inputOutside, _, _⟩ := signatureBuffers call size
  obtain ⟨ret, retSlot, retLow, retOutside⟩ := call.returnAddress
  have pre := signatureFramePre call (memLoad_returnSlot retSlot) retLow retOutside
  have window : Writable Extracted.programImage initial.external (sp - 656) 656 :=
    pre.window (by decide)
  have output : Writable Extracted.programImage initial.external fr.rdi 72 :=
    window.of_offsets (addr_sub sp 80) (addr_sub sp 656) (by decide)
  have pushFrame := pairPushFrame call.stackAvailable
  have low : fr.rsi.toNat + 64 ≤ 2 ^ 32 := input.low
  have outputLow := output.readable.low
  have stackEnd : stack.start + stack.size = sp.toNat + 8 := stackRegionEnd _ _
  have callStackStart : (callStack fr).start = stack.start :=
    Activation.ofEntry_low_toNat (ret := 0x102468)
  have callRsp : fr.rsp.toNat = sp.toNat - 96 := stackSubToNat (by omega : 96 ≤ sp.toNat)
  have callStackEnd : (callStack fr).start + (callStack fr).size = sp.toNat - 88 := by
    change (callStack fr).start + (fr.rsp.toNat + 8 - (callStack fr).start) = _
    rw [callStackStart, callRsp]
    change sp.toNat - 784 + (sp.toNat - 96 + 8 - (sp.toNat - 784)) = _
    omega
  have outputStart : fr.rdi.toNat = sp.toNat - 80 := stackSubToNat (by omega : 80 ≤ sp.toNat)
  have inputApart : fr.rsi.toNat + 64 ≤ stack.start ∨ stack.start + stack.size ≤ fr.rsi.toNat :=
    inputOutside.2 stack List.mem_cons_self
  refine ⟨input.of_frame pushFrame, output.of_frame pushFrame, ⟨inputOutside.1, ?_⟩,
    ⟨by omega, ?_⟩, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [callStackEnd, callStackStart]
    rw [stackEnd] at inputApart
    rcases inputApart with h | h <;> omega
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [callStackEnd, outputStart]
    exact Or.inr (by omega)
  · intro j hj
    apply pushFrame.memLoad_eq
    have wordStart : (wordAddr fr.rsi 64 j).toNat = fr.rsi.toNat + 8 * j := by
      change (fr.rsi + BitVec.ofNat 64 (8 * j)).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_⟩
    · rw [wordStart]
      change fr.rsi.toNat + 8 * j + 8 ≤ 2 ^ 64
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [wordStart]
      change fr.rsi.toNat + 8 * j + 8 ≤ stack.start ∨ stack.start + stack.size ≤ fr.rsi.toNat + 8 * j
      rcases inputApart with h | h <;> omega

theorem pairWrites {initial : RamState} {bytes : ByteArray} {mem : Ram}
    (call : ValidCall signatureFromSlice initial [bytes])
    (writes : let fr := pairFrame initial
      RamWriteFrame fr.original mem [fr.region, buffer fr.rdi 72]) :
    let sp := initial.regValue .rsp
    RamWriteFrame initial.external mem [Stack.region initial signatureFromSlice.minStackBytes] ∧
      memLoad mem (sp - 8) 64 = initial.regValue .rbx ∧
      memLoad mem sp 64 = memLoad initial.external sp 64 := by
  intro sp
  let fr := pairFrame initial
  let stack := Stack.region initial signatureFromSlice.minStackBytes
  obtain ⟨room, low⟩ : 784 ≤ sp.toNat ∧ sp.toNat + 8 < 2 ^ 32 :=
    stackBounds call.stackAvailable
  have rsp : fr.rsp.toNat = sp.toNat - 96 := stackSubToNat (by omega : 96 ≤ sp.toNat)
  have start : fr.region.start = stack.start :=
    Activation.ofEntry_low_toNat (ret := 0x102468)
  have stackEnd : stack.start + stack.size = sp.toNat + 8 := stackRegionEnd _ _
  have frameEnd : fr.region.start + fr.region.size = sp.toNat - 96 := by
    change fr.region.start + (fr.rsp.toNat - fr.region.start) = _
    rw [rsp, start]
    change sp.toNat - 784 + (sp.toNat - 96 - (sp.toNat - 784)) = _
    omega
  have bufferStart : (buffer fr.rdi 72).start = sp.toNat - 80 :=
    stackSubToNat (by omega : 80 ≤ sp.toNat)
  have bufferEnd : (buffer fr.rdi 72).start + (buffer fr.rdi 72).size = sp.toNat - 8 := by
    change (buffer fr.rdi 72).start + 72 = _
    rw [bufferStart]
    omega
  have subset : RegionsWithin [fr.region, buffer fr.rdi 72] [stack] := by
    intro r hr
    refine ⟨stack, List.mem_cons_self, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [frameEnd, start, stackEnd]
      omega
    · rw [bufferEnd, bufferStart, stackEnd]
      change sp.toNat - 784 ≤ _ ∧ _
      omega
  have after {a : BitVec 64} (ha : sp.toNat - 8 ≤ a.toNat) (hbound : a.toNat + 8 ≤ 2 ^ 64) :
      Outside [fr.region, buffer fr.rdi 72] a 8 := by
    refine ⟨hbound, fun r hr => Or.inr ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [frameEnd]
      omega
    · rw [bufferEnd]
      exact ha
  have saved : (sp - 8).toNat = sp.toNat - 8 := stackSubToNat (by omega : 8 ≤ sp.toNat)
  have savedOutside : Outside [fr.region, buffer fr.rdi 72] (sp - 8) 8 :=
    after (by rw [saved]; exact Nat.le_refl _) (by rw [saved]; omega)
  have returnOutside : Outside [fr.region, buffer fr.rdi 72] sp 8 :=
    after (by omega) (by omega)
  change RamWriteFrame fr.original mem [fr.region, buffer fr.rdi 72] at writes
  let save := memStore initial.external (sp - 8) (initial.regValue .rbx)
  have original : fr.original = memStore save (sp - 96) (0x102468 : BitVec 64) := rfl
  have pushApart : RangeApart (sp - 96) 8 (sp - 8) 8 :=
    RangeApart.of_offsets (addr_sub sp 96) (addr_sub sp 8) (by decide)
  refine ⟨(pairPushFrame call.stackAvailable).trans writes subset, ?_, ?_⟩
  · rw [writes.memLoad_eq savedOutside, original,
      memLoad_memStore_of_rangeApart save _ _ _ _ pushApart]
    exact memLoad_memStore_same initial.external _ _ (by decide) (by decide)
  · have retApart96 : RangeApart (sp - 96) 8 sp 8 :=
      RangeApart.of_offsets (addr_sub sp 96) (addr_self sp) (by decide)
    have retApart8 : RangeApart (sp - 8) 8 sp 8 :=
      RangeApart.of_offsets (addr_sub sp 8) (addr_self sp) (by decide)
    rw [writes.memLoad_eq returnOutside, original,
      memLoad_memStore_of_rangeApart save _ _ _ _ retApart96,
      memLoad_memStore_of_rangeApart initial.external _ _ _ _ retApart8]

end K256.Proofs.ParseSignature.Wrapper
