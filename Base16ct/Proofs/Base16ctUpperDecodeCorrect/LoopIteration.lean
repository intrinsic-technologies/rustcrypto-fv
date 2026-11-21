import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.MachineInvariant
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Memory

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def DecodeLoopStep [Bindings] (routine : Routine) (alphabets : List RFC4648.Alphabet)
    (exitOffset steps : Nat) : Prop :=
  ∀    {initial s : RamState} {input : List UInt8} {capacity count : Nat}
    {boundary : ReturnBoundary} {high low : UInt8}
    (_hvalid : ValidCall routine initial input capacity lengthWritten)
    (_hentry : EntryReady programImage s)
    (_hp : s.RIP = routine.entryAddress + 48#64) (_hret : ¬ InProgram boundary.rip)
    (_hcount : count < capacity)
    (_hrcx : AddrMode.reg64 1 s = AddrMode.reg64 1 initial)
    (_hrax : AddrMode.reg64 0 s = BitVec.ofNat 64 count)
    (_halloc : (outputRegion initial capacity).Allocated s.external)
    (_hload1 : MemReadable s ((AddrMode.sib 7 (some 0) 1#2 .none).addrAt s 5) 1)
    (_hload2 : MemReadable s ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) 1)
    (_hfirst : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addrAt s 5) :
      Operand 8).read s = high.toBitVec)
    (_hsecond : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) :
      Operand 8).read s = low.toBitVec),
    ∃ t, Advances boundary steps s t ∧ EntryReady programImage t ∧
      t.RIP = (if AddrMode.reg64 9 s = BitVec.ofNat 64 count + 1#64
        then routine.entryAddress + BitVec.ofNat 64 exitOffset else routine.entryAddress + 48#64) ∧
      AgreesExcept [.reg 0, .reg 3, .reg 5, .reg 6, .reg 8, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t ∧
      t.external = memStore s.external (lowerStoreAM.addrAt s 3)
        ((decodePair alphabets high low).setWidth 8) ∧
      AddrMode.reg64 0 t = BitVec.ofNat 64 (count + 1) ∧
      AddrMode.reg64 6 t = (((Operand.reg 6#5 : Operand 32).read s) |||
        ((decodePair alphabets high low).extractLsb' 8 8).setWidth 32).setWidth 64

set_option maxRecDepth 100000 in
theorem decode_machine_loop_step_values [Bindings]
    {initial s : RamState} {input processed rest : List UInt8} {high low : UInt8}
    {regions : Vector MemoryRegion n} {components : List Component} {capacity : Nat}
    {boundary : ReturnBoundary}
    (hstep : DecodeLoopStep (lengthWritten := lengthWritten) routine alphabets exitOffset steps)
    (hstack : 16 ≤ routine.minStackBytes)
    (hvalid : ValidCall routine initial input capacity lengthWritten)
    (hentry : EntryReady programImage s)
    (h : DecodeMachineLoopInvariant alphabets routine.entryAddress exitOffset initial input processed
      (high :: low :: rest) regions components s)
    (heven : input.length % 2 = 0) (hcapacity : input.length / 2 ≤ capacity)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary steps s t ∧ EntryReady programImage t ∧
      t.RIP = (if rest = [] then routine.entryAddress + BitVec.ofNat 64 exitOffset else routine.entryAddress + 48#64) ∧
      AgreesExcept [.reg 0, .reg 3, .reg 5, .reg 6, .reg 8, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t ∧
      t.external = memStore s.external (lowerStoreAM.addrAt s 3)
        ((decodePair alphabets high low).setWidth 8) ∧
      AddrMode.reg64 0 t = BitVec.ofNat 64 ((processed ++ [high, low]).length / 2) ∧
      AddrMode.reg64 6 t = (decodeLoop alphabets (processed ++ [high, low])).2.setWidth 64 ∧
      (outputRegion initial capacity).Allocated t.external ∧
      readOutput initial t ((processed ++ [high, low]).length / 2) =
        .ok (decodeLoop alphabets (processed ++ [high, low])).1 ∧
      DirectionFlagUnset t ∧
      MemoryWriteFrame s t #v[outputRegion initial (input.length / 2)] ∧
      (∀ i : Fin input.length,
        t.external[BitVec.ofNat 64 ((inputRegion initial input.toByteArray).start + i.val)]? =
          initial.external[BitVec.ofNat 64 ((inputRegion initial input.toByteArray).start + i.val)]?) ∧
      Machine.loadBytes t.external (AddrMode.reg64 4 t) 8 = .ok (AddrMode.reg64 3 initial) ∧
      Machine.loadBytes t.external (AddrMode.reg64 4 t + 8#64) 8 = .ok (AddrMode.reg64 5 initial) := by
  have hlen : input.length = processed.length + rest.length + 2 := by
    rw [h.split]
    simp only [List.length_append, List.length_cons]
    omega
  have hindex0 : processed.length + 0 < input.length := by omega
  have hindex1 : processed.length + 1 < input.length := by omega
  have hbyte0 := decode_machine_head_byte hvalid h hindex0
  have hbyte1 := decode_machine_head_byte hvalid h hindex1
  have hfirst : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addrAt s 5) :
      Operand 8).read s = high.toBitVec := by
    have hx : input[processed.length] = high := by
      simp [h.split]
    simpa [AddrMode.addrAt, AddrMode.addr, Disp.value, Operand.read, hx] using hbyte0
  have hsecond : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) :
      Operand 8).read s = low.toBitVec := by
    have hx : input[processed.length + 1] = low := by
      simp [h.split]
    simpa [AddrMode.addrAt, AddrMode.addr, Disp.value, Operand.read, hx] using hbyte1
  have halloc : (outputRegion initial capacity).Allocated s.external := by
    have ha := h.outputAllocated
    rw [outputCapacity hvalid] at ha
    exact ha
  have hcount : processed.length / 2 < capacity := by omega
  obtain ⟨t, ha, ht, hpt, hf, hm, hax, hsi⟩ := hstep
    hvalid hentry (h.headRip (by simp)) hret hcount h.rcx h.rax halloc
    (decode_machine_head_load1 hvalid h (by simp))
    (decode_machine_head_load2 hvalid h (by simp)) hfirst hsecond
  have hbranch : AddrMode.reg64 9 s = BitVec.ofNat 64 (processed.length / 2) + 1#64 ↔ rest = [] := by
    rw [h.r9]
    have hsum : BitVec.ofNat 64 (processed.length / 2) + 1#64 =
        BitVec.ofNat 64 (processed.length / 2 + 1) := by simp [BitVec.ofNat_add]
    rw [hsum]
    have hi : input.length / 2 < 2^64 := by have := inputLengthBound hvalid; omega
    have hp : processed.length / 2 + 1 < 2^64 := by have := inputLengthBound hvalid; omega
    constructor
    · intro heq
      have hn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp] at hn
      have hpEven := h.processedEven
      have hz : rest.length = 0 := by omega
      cases rest <;> simp_all
    · intro hz
      subst rest
      simp only [List.length_nil] at hlen
      congr 1
      omega
  have hsi32 : (Operand.reg 6#5 : Operand 32).read s =
      (decodeLoop alphabets processed).2.setWidth 32 := by
    have hh := congrArg (fun x : BitVec 64 => x.setWidth 32) h.rsi
    simpa [AddrMode.reg64, Operand.read] using hh
  have hnewsi : AddrMode.reg64 6 t =
      (decodeLoop alphabets (processed ++ [high, low])).2.setWidth 64 := by
    rw [hsi, hsi32, decodeLoop_append_even _ _ _ h.processedEven]
    simp only [decodeLoop, BitVec.setWidth_or]
    simp
  have haddr : lowerStoreAM.addrAt s 3 =
      initial.regValue .rcx + BitVec.ofNat 64 (processed.length / 2) := by
    simp only [lowerStoreAM, AddrMode.addrAt, AddrMode.addr, h.rcx, h.rax, Disp.value]
    change AddrMode.reg64 1 initial + (BitVec.ofNat 64 (processed.length / 2) <<< 0) + 0#64 = _
    simp only [BitVec.shiftLeft_zero, BitVec.add_zero]
    rfl
  have houtput := readOutput_store_next
    (byte := UInt8.ofBitVec ((decodePair alphabets high low).setWidth 8))
    (by have := inputLengthBound hvalid; omega : processed.length / 2 < 2^64)
    h.output (by simpa only [haddr] using hm)
  have hframeFor (length : Nat) (hlen : length ≤ capacity)
      (hindex : processed.length / 2 < length) :
      MemoryWriteFrame s t #v[outputRegion initial length] := by
    apply hf.memoryWriteFrame
    intro c hc x hcov
    have hc' : c = .mem (lowerStoreAM.addrAt s 3) 1 := by
      cases c <;> simp_all [Component.Covers]
    subst c
    obtain ⟨i, hi, rfl⟩ := hcov
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨outputRegion initial length, by simp, ?_⟩
    rw [BitVec.add_zero, haddr]
    have hb : (outputRegion initial length).Bounded := by
      have hb := hvalid.outputInMemory.2.1
      change (initial.regValue .rcx).toNat + capacity < 2^32 at hb
      change (initial.regValue .rcx).toNat + length < 2^32
      omega
    have hc := region_contains_offset hb hindex
    simpa [outputRegion, registerRegion, BitVec.ofNat_add] using hc
  have hframe := hframeFor capacity (Nat.le_refl _) hcount
  have hframeOutput := hframeFor (input.length / 2) hcapacity (by omega)
  have hinput : ∀ i : Fin input.length,
      t.external[BitVec.ofNat 64 ((inputRegion initial input.toByteArray).start + i.val)]? =
        initial.external[BitVec.ofNat 64 ((inputRegion initial input.toByteArray).start + i.val)]? := by
    intro i
    apply (hframe _ ?_).trans (h.inputUnchanged i)
    intro region hregion
    simp only [Vector.mem_singleton] at hregion
    subst region
    have hi := region_contains_offset hvalid.inputInMemory.2.1
      (by simpa only [inputRegion, registerRegion, List.size_toByteArray] using i.isLt)
    exact hvalid.separation.1 (0 : Fin 3) (1 : Fin 3) (by decide) _ hi
  have hrsp : AddrMode.reg64 4 t = AddrMode.reg64 4 s := hf.read (by simp)
  have hstackPreserved (offset : Nat) (hoffset : offset + 8 ≤ 16) :
      Machine.loadBytes t.external (AddrMode.reg64 4 t + BitVec.ofNat 64 offset) 8 =
        Machine.loadBytes s.external (AddrMode.reg64 4 s + BitVec.ofNat 64 offset) 8 := by
    rw [hrsp]
    apply loadBytes_eq_of_bytes_eq
    intro i hi
    apply hframe _
    intro region hregion
    simp only [Vector.mem_singleton] at hregion
    subst region
    intro hout
    have hn := hvalid.stack.2.2.1
    change routine.minStackBytes ≤ (initial.regValue .rsp).toNat at hn
    have hb := (initial.regValue .rsp).isLt
    have haddr' : AddrMode.reg64 4 s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
        BitVec.ofNat 64 ((Stack.region initial routine.minStackBytes).start +
          (routine.minStackBytes - 16 + offset + i)) := by
      rw [h.rsp]
      change initial.regValue .rsp - 16#64 + BitVec.ofNat 64 offset + BitVec.ofNat 64 i = _
      have hsub : initial.regValue .rsp - 16#64 = BitVec.ofNat 64 ((initial.regValue .rsp).toNat - 16) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le (by change 16 ≤ (initial.regValue .rsp).toNat; omega)]
        simp only [BitVec.toNat_ofNat]
        omega
      rw [hsub, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      change (initial.regValue .rsp).toNat - 16 + offset + i =
        (initial.regValue .rsp).toNat - routine.minStackBytes + (routine.minStackBytes - 16 + offset + i)
      omega
    have hsize : routine.minStackBytes - 16 + offset + i < (Stack.region initial routine.minStackBytes).size := by
      change routine.minStackBytes - 16 + offset + i <
        (initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - routine.minStackBytes)
      omega
    have hstackMem := region_contains_offset hvalid.stack.1 hsize
    rw [haddr'] at hout
    exact hvalid.separation.1 (1 : Fin 3) (2 : Fin 3) (by decide) _ hout hstackMem
  have hsaved : Machine.loadBytes t.external (AddrMode.reg64 4 t) 8 = .ok (AddrMode.reg64 3 initial) := by
    simpa only [BitVec.add_zero] using (hstackPreserved 0 (by omega)).trans (by simpa only [BitVec.add_zero] using h.savedRBX)
  have hsavedBP : Machine.loadBytes t.external (AddrMode.reg64 4 t + 8#64) 8 = .ok (AddrMode.reg64 5 initial) :=
    (hstackPreserved 8 (by omega)).trans h.savedRBP
  refine ⟨t, ha, ht, ?_, hf, hm, ?_, hnewsi, ?_, ?_,
    hf.directionFlagClear (by simp) h.directionFlagUnset, hframeOutput, hinput, hsaved, hsavedBP⟩
  · simpa only [hbranch] using hpt
  · simpa only [List.length_append, List.length_cons, List.length_nil,
      show (processed.length + (1 + (1 + 0))) / 2 = processed.length / 2 + 1 by omega] using hax
  · rw [hm]
    exact allocated_memStore halloc _ _
  · rw [decodeLoop_append_even _ _ _ h.processedEven]
    simp only [decodeLoop]
    have hlen' : (processed ++ [high, low]).length / 2 = processed.length / 2 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlen']
    exact houtput

set_option maxRecDepth 100000 in
theorem decode_machine_loop_preserves [Bindings]
    {initial s : RamState} {input processed rest : List UInt8} {high low : UInt8}
    {regions : Vector MemoryRegion n} {components : List Component} {capacity : Nat}
    {boundary : ReturnBoundary}
    (hstep : DecodeLoopStep (lengthWritten := lengthWritten) routine alphabets exitOffset steps)
    (hstack : 16 ≤ routine.minStackBytes)
    (hvalid : ValidCall routine initial input capacity lengthWritten)
    (hentry : EntryReady programImage s)
    (h : DecodeMachineLoopInvariant alphabets routine.entryAddress exitOffset initial input processed
      (high :: low :: rest) regions components s)
    (heven : input.length % 2 = 0) (hcapacity : input.length / 2 ≤ capacity)
    (hret : ¬ InProgram boundary.rip)
    (hregion : outputRegion initial (input.length / 2) ∈ regions)
    (hallowed : ∀ c ∈ decodeLoopEffects initial (input.length / 2), c ∈ components) :
    ∃ t, Advances boundary steps s t ∧ EntryReady programImage t ∧
      DecodeMachineLoopInvariant alphabets routine.entryAddress exitOffset initial input (processed ++ [high, low])
        rest regions components t := by
  obtain ⟨t, ha, ht, hpt, hf, _, hax, hsi, hal, hout, hdf, hm, hin, hsave, hsaveBP⟩ :=
    decode_machine_loop_step_values hstep hstack hvalid hentry h heven hcapacity hret
  have hlen : input.length = processed.length + rest.length + 2 := by
    rw [h.split]
    simp only [List.length_append, List.length_cons]
    omega
  have hcount : processed.length / 2 < capacity := by omega
  have haddr : lowerStoreAM.addrAt s 3 =
      initial.regValue .rcx + BitVec.ofNat 64 (processed.length / 2) := by
    simp only [lowerStoreAM, AddrMode.addrAt, AddrMode.addr, h.rcx, h.rax, Disp.value]
    change AddrMode.reg64 1 initial + (BitVec.ofNat 64 (processed.length / 2) <<< 0) + 0#64 = _
    simp only [BitVec.shiftLeft_zero, BitVec.add_zero]
    rfl
  have hwide : AgreesExcept (decodeLoopEffects initial (input.length / 2)) s t := by
    apply hf.widen
    · intro c hc hmem
      cases c <;> simp_all [decodeLoopEffects, Component.isMem]
    · intro x c hc hcov
      have hc' : c = .mem (lowerStoreAM.addrAt s 3) 1 := by
        cases c <;> simp_all [Component.Covers]
      subst c
      obtain ⟨i, hi, rfl⟩ := hcov
      have hi0 : i = 0 := by omega
      subst i
      refine ⟨.mem (initial.regValue .rcx) (input.length / 2), by simp [decodeLoopEffects], ?_⟩
      refine ⟨processed.length / 2, by omega, ?_⟩
      rw [BitVec.add_zero, haddr]
  have hfull : AgreesExcept components initial t := by
    apply (h.agrees.trans (hwide.mono hallowed)).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc
  have hmem : MemoryWriteFrame initial t regions := by
    apply memoryWriteFrame_trans h.frame
    intro x hx
    exact hm x (by intro region hreg; simp only [Vector.mem_singleton] at hreg; subst region; exact hx _ hregion)
  refine ⟨t, ha, ht, ?_⟩
  refine {
    split := ?_
    processedEven := ?_
    rip := hpt
    rax := hax
    rsi := hsi
    rdi := ?_
    rcx := ?_
    r9 := ?_
    rsp := ?_
    rdx := ?_
    savedRBX := hsave
    savedRBP := hsaveBP
    output := hout
    inputUnchanged := hin
    outputAllocated := ?_
    directionFlagUnset := hdf
    frame := hmem
    agrees := hfull }

  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using h.split
  · have he := h.processedEven
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · exact (hf.read (by simp)).trans h.rdi
  · exact (hf.read (by simp)).trans h.rcx
  · exact (hf.read (by simp)).trans h.rdx
  · exact (hf.read (by simp)).trans h.r9
  · exact (hf.read (by simp)).trans h.rsp
  · rw [outputCapacity hvalid]
    exact hal

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
