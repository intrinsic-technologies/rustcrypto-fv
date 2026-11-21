import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopConcrete
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

structure DecodeMachineLoopInvariant (alphabets : List RFC4648.Alphabet)
    (entry : BitVec 64) (exitOffset : Nat)
    (entryState : RamState) (input processed rest : List UInt8) (regions : Vector MemoryRegion n)
    (components : List Component) (s : RamState) : Prop where
  split : input = processed ++ rest
  processedEven : processed.length % 2 = 0
  rip : s.RIP = if rest = [] then entry + BitVec.ofNat 64 exitOffset else entry + 48#64
  rax : AddrMode.reg64 0 s = BitVec.ofNat 64 (processed.length / 2)
  rsi : AddrMode.reg64 6 s = (decodeLoop alphabets processed).2.setWidth 64
  rdi : AddrMode.reg64 7 s = AddrMode.reg64 7 entryState
  rcx : AddrMode.reg64 1 s = AddrMode.reg64 1 entryState
  rdx : AddrMode.reg64 2 s = AddrMode.reg64 2 entryState
  r9 : AddrMode.reg64 9 s = BitVec.ofNat 64 (input.length / 2)
  rsp : AddrMode.reg64 4 s = AddrMode.reg64 4 entryState - 16#64
  savedRBX : Machine.loadBytes s.external (AddrMode.reg64 4 s) 8 =
    .ok (AddrMode.reg64 3 entryState)
  savedRBP : Machine.loadBytes s.external (AddrMode.reg64 4 s + 8#64) 8 =
    .ok (AddrMode.reg64 5 entryState)
  output : readOutput entryState s (processed.length / 2) = .ok (decodeLoop alphabets processed).1
  inputUnchanged : ∀ i : Fin input.length,
    s.external[BitVec.ofNat 64 ((inputRegion entryState input.toByteArray).start + i.val)]? =
      entryState.external[BitVec.ofNat 64 ((inputRegion entryState input.toByteArray).start + i.val)]?
  outputAllocated :
    (outputRegion entryState (entryState.regValue .r8).toNat).Allocated s.external
  directionFlagUnset : DirectionFlagUnset s
  frame : MemoryWriteFrame entryState s regions
  agrees : AgreesExcept components entryState s

theorem DecodeMachineLoopInvariant.headRip
    (h : DecodeMachineLoopInvariant alphabets entry exitOffset entryState input processed rest regions components s)
    (hrest : 2 ≤ rest.length) : s.RIP = entry + 48#64 := by
  have hne : rest ≠ [] := by intro he; subst rest; simp at hrest
  simpa only [ite_eq_right hne] using h.rip

set_option maxRecDepth 100000 in
 theorem decode_machine_head_load1 {entryState s : RamState}
    {input processed rest : List UInt8} {regions : Vector MemoryRegion n} {components : List Component}
    {capacity : Nat}
    (hvalid : ValidCall routine entryState input capacity lengthWritten)
    (h : DecodeMachineLoopInvariant alphabets entry exitOffset entryState input processed rest regions components s)
    (hrest : 2 ≤ rest.length) : MemReadable s
      ((AddrMode.sib 7 (some 0) 1#2 .none).addr s (BitVec.add s.RIP (5#64))) 1 := by
  let region := inputRegion entryState input.toByteArray
  have hb := hvalid.inputInMemory.2.1
  have hbytes := hvalid.inputInMemory.2.2
  have hlen : input.length = region.size := by
    simpa [region, inputRegion, MemoryRegion.HasLength] using hbytes.1
  have hpre : processed.length < input.length := by
    rw [h.split]
    simp only [List.length_append]
    omega
  have haddr : (AddrMode.sib 7 (some 0) 1#2 .none).addr s
      (BitVec.add s.RIP (5#64)) = BitVec.ofNat 64 (region.start + processed.length) := by
    simp [AddrMode.addr, Disp.value]
    have hrdi := h.rdi
    have hrax := h.rax
    simp only [AddrMode.reg64] at hrdi hrax ⊢
    change AddrMode.reg64 (7#4) s + AddrMode.reg64 (0#4) s <<< 1 = _
    have hrdi' : AddrMode.reg64 (7#4) s = AddrMode.reg64 (7#4) entryState := by simpa using h.rdi
    have hrax' : AddrMode.reg64 (0#4) s = BitVec.ofNat 64 (processed.length / 2) := by simpa using h.rax
    rw [hrdi', hrax']
    have hr : AddrMode.reg64 (7#4) entryState = entryState.regValue .rdi := by rfl
    rw [hr]
    have hshift : (BitVec.ofNat 64 (processed.length / 2)) <<< 1 =
        BitVec.ofNat 64 processed.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat]
      have he := h.processedEven
      have hq : processed.length / 2 < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hn : processed.length < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hs : (processed.length / 2) <<< 1 < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hmods : ((processed.length / 2) <<< 1) % 2^64 =
          (processed.length / 2) <<< 1 := Nat.mod_eq_of_lt hs
      rw [Nat.mod_eq_of_lt hq, hmods, Nat.mod_eq_of_lt hn]
      omega
    rw [hshift]
    simp [region, inputRegion, registerRegion, BitVec.ofNat_add]
  rw [haddr]
  refine ⟨?_, ?_⟩
  · have hnat : (BitVec.ofNat 64 (region.start + processed.length)).toNat =
        region.start + processed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change region.start + region.size < 2 ^ 32 at hb
      rw [← hlen] at hb
      omega
    rw [hnat]
    change region.start + region.size < 2 ^ 32 at hb
    rw [← hlen] at hb
    omega
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    apply Option.isSome_iff_exists.mpr
    let hi' : Fin input.length := ⟨processed.length, hpre⟩
    let hiB : Fin input.toByteArray.size := ⟨processed.length, by simpa using hpre⟩
    have hu := h.inputUnchanged hi'
    have hv := hbytes.2 hiB
    have heq : BitVec.ofNat 64 (region.start + processed.length) =
        BitVec.ofNat 64 ((inputRegion entryState input.toByteArray).start + hi'.val) := by
      rfl
    rw [← heq] at hu
    simpa using ⟨_, hu.trans hv⟩
set_option maxRecDepth 100000 in
 theorem decode_machine_head_load2 {entryState s : RamState}
    {input processed rest : List UInt8} {regions : Vector MemoryRegion n} {components : List Component}
    {capacity : Nat}
    (hvalid : ValidCall routine entryState input capacity lengthWritten)
    (h : DecodeMachineLoopInvariant alphabets entry exitOffset entryState input processed rest regions components s)
    (hrest : 2 ≤ rest.length) : MemReadable s
      ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s (BitVec.add s.RIP (6#64))) 1 := by
  let region := inputRegion entryState input.toByteArray
  have hb := hvalid.inputInMemory.2.1
  have hbytes := hvalid.inputInMemory.2.2
  have hlen : input.length = region.size := by
    simpa [region, inputRegion, MemoryRegion.HasLength] using hbytes.1
  have hpre : processed.length + 1 < input.length := by
    rw [h.split]
    simp only [List.length_append]
    omega
  have haddr : (AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s
      (BitVec.add s.RIP (6#64)) = BitVec.ofNat 64 (region.start + processed.length + 1) := by
    simp [AddrMode.addr, Disp.value]
    have hrdi' : AddrMode.reg64 (7#4) s = AddrMode.reg64 (7#4) entryState := by simpa using h.rdi
    have hrax' : AddrMode.reg64 (0#4) s = BitVec.ofNat 64 (processed.length / 2) := by simpa using h.rax
    rw [hrdi', hrax']
    have hr : AddrMode.reg64 (7#4) entryState = entryState.regValue .rdi := by rfl
    rw [hr]
    have hshift : (BitVec.ofNat 64 (processed.length / 2)) <<< 1 =
        BitVec.ofNat 64 processed.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat]
      have he := h.processedEven
      have hq : processed.length / 2 < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hn : processed.length < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hs : (processed.length / 2) <<< 1 < 2^64 := by
        have hi := inputLengthBound hvalid
        omega
      have hmods : ((processed.length / 2) <<< 1) % 2^64 =
          (processed.length / 2) <<< 1 := Nat.mod_eq_of_lt hs
      rw [Nat.mod_eq_of_lt hq, hmods, Nat.mod_eq_of_lt hn]
      omega
    rw [hshift]
    simp [region, inputRegion, registerRegion, BitVec.ofNat_add]
  rw [haddr]
  refine ⟨?_, ?_⟩
  · have hnat : (BitVec.ofNat 64 (region.start + processed.length + 1)).toNat =
        region.start + processed.length + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change region.start + region.size < 2 ^ 32 at hb
      rw [← hlen] at hb
      omega
    rw [hnat]
    change region.start + region.size < 2 ^ 32 at hb
    rw [← hlen] at hb
    omega
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    apply Option.isSome_iff_exists.mpr
    let hi' : Fin input.length := ⟨processed.length + 1, hpre⟩
    let hiB : Fin input.toByteArray.size := ⟨processed.length + 1, by simpa using hpre⟩
    have hu := h.inputUnchanged hi'
    have hv := hbytes.2 hiB
    dsimp [hi', hiB] at hu hv
    simp only [BitVec.add_zero]
    simpa [region] using ⟨_, hu.trans hv⟩

theorem decode_machine_head_byte {entryState s : RamState}
    {input processed rest : List UInt8} {regions : Vector MemoryRegion n}
    {components : List Component} {capacity offset : Nat}
    (hvalid : ValidCall routine entryState input capacity lengthWritten)
    (h : DecodeMachineLoopInvariant alphabets entry exitOffset entryState input processed rest regions components s)
    (hi : processed.length + offset < input.length) :
    memLoad s.external (AddrMode.reg64 7 s + (AddrMode.reg64 0 s <<< 1) +
      BitVec.ofNat 64 offset) 8 = input[processed.length + offset].toBitVec := by
  have hshift : (BitVec.ofNat 64 (processed.length / 2)) <<< 1 =
      BitVec.ofNat 64 processed.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat]
    have he := h.processedEven
    have hb := inputLengthBound hvalid
    have hq : processed.length / 2 < 2^64 := by omega
    have hn : processed.length < 2^64 := by omega
    have hs : (processed.length / 2) <<< 1 < 2^64 := by omega
    rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
    omega
  have hr : AddrMode.reg64 7 entryState = entryState.regValue .rdi := rfl
  have haddr : AddrMode.reg64 7 s + (AddrMode.reg64 0 s <<< 1) + BitVec.ofNat 64 offset =
      BitVec.ofNat 64 ((inputRegion entryState input.toByteArray).start + (processed.length + offset)) := by
    rw [h.rdi, h.rax, hshift, hr]
    simp [inputRegion, registerRegion, BitVec.ofNat_add, BitVec.add_assoc]
  rw [haddr, memLoad_8]
  have hu := h.inputUnchanged ⟨processed.length + offset, hi⟩
  have hb := hvalid.inputInMemory.2.2.2 ⟨processed.length + offset, by simpa using hi⟩
  have hbyte : s.external[BitVec.ofNat 64 ((inputRegion entryState input.toByteArray).start +
      (processed.length + offset))]? = some input[processed.length + offset] := by
    exact hu.trans (by simpa using hb)
  simp only [memByte, PhysicalMemory.read, hbyte, Option.getD_some]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
