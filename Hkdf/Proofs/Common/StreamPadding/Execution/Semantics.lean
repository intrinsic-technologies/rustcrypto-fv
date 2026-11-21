import Hkdf.Proofs.Common.StreamPadding.Stages
import Hkdf.Proofs.Common.StreamPadding.Interface
import Hkdf.Proofs.Common.StreamPadding.Mathematics

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.Instructions

theorem load_observations {s t : RamState} {message : ByteArray} (v : Variant)
    (effect : (Stages.loadEffect v s).Holds s t)
    (stream : StreamAt s (rspOf s + BitVec.ofNat 64 v.tail) message) :
    t.regValue v.hashReg = rspOf s + BitVec.ofNat 64 v.hash ∧
    t.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64) ∧
    t.regValue v.blocksReg = BitVec.ofNat 64 (message.size / 64) ∧
    t.regValue v.remainingReg = BitVec.ofNat 64 (63 - message.size % 64) ∧
    t.external = s.external := by
  have tailRead : (memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+63)) 8).setWidth 64 =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [memLoad_8]
    change ((s.external[rspOf s + BitVec.ofNat 64 (v.tail+63)]?).getD (0 : UInt8)).toBitVec.setWidth 64 = _
    have tail := stream.tailLength
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] at tail
    rw [tail]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec, UInt8.toNat_ofNat']
    have := Nat.mod_lt message.size (by decide : 0 < 64)
    omega
  have blocks : memLoad s.external (rspOf s + BitVec.ofNat 64 v.counter) 64 =
      BitVec.ofNat 64 (message.size/64) := by
    apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Variant.counter, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using stream.blocks
  have writes := effect.writes
  simp only [Stages.loadEffect, Write.AllHold, Variant.hashIndex, Variant.lengthIndex, Variant.blocksIndex,
    Variant.remainingIndex, read_regIndex, BitVec.setWidth_eq] at writes
  refine ⟨writes.1, writes.2.1.trans tailRead, writes.2.2.1.trans blocks, ?_, ?_⟩
  · have r15 := writes.2.2.2
    change t.regValue v.remainingReg = (memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+63)) 8).setWidth 64 ^^^ 63 at r15
    rw [r15, tailRead]
    exact tail_zero_count _ (Nat.mod_lt _ (by decide))
  · apply effect.agrees.external
    simp [Stages.loadEffect, Effect.components, Write.component, Operand.component, Component.Covers]

theorem mark_bytes {s t : RamState} {message : ByteArray} (v : Variant)
    (effect : (Stages.markEffect v s).Holds s t)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64))
    (source : (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,message.size % 64⟩ : MemoryRegion).HasBytes
      s.external (remainderBytes message)) :
    t.external[rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 (message.size % 64)]? = some 128 ∧
    (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,message.size % 64⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes message) := by
  have address : rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail =
      rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 (message.size % 64) := by
    simp only [Variant.lengthIndex, read_regIndex, BitVec.setWidth_eq]
    rw [remainder]
    bv_omega
  have marker := effect.writes.1
  change memLoad t.external (rspOf s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail) 8 = 128 at marker
  rw [address, memLoad_8] at marker
  have byte : memByte t.external
      (rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 (message.size % 64)) = 128 :=
    UInt8.toBitVec_inj.mp marker
  constructor
  · cases found : t.external[rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 (message.size % 64)]? with
    | none =>
      simp only [memByte, PhysicalMemory.read, found, Option.getD_none] at byte
      exact False.elim ((by decide : (0 : UInt8) ≠ 128) byte)
    | some value => simpa only [memByte, PhysicalMemory.read, found, Option.getD_some] using congrArg some byte
  · refine ⟨source.1, fun i => ?_⟩
    apply Eq.trans (effect.agrees.byte ?_) (source.2 i)
    intro c hc covered
    simp only [Stages.markEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, he⟩ := covered
    have hi : i.val < message.size % 64 := by simpa only [remainderBytes_size] using i.isLt
    have remBound := Nat.mod_lt message.size (by decide : 0 < 64)
    have apart := RangeApart.offsets (rspOf s + BitVec.ofNat 64 v.tail)
      (a := message.size % 64) (len := 1) (b := 0) (count := message.size % 64)
      (by omega) (by omega) (.inr (by omega))
    apply apart j hj i.val hi
    simpa only [address, BitVec.add_zero, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using he.symm

theorem zero_words {s t : RamState} (v : Variant)
    (effect : (Stages.zeroEffect v s).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + BitVec.ofNat 64 (v.tail+8*j)) 64 = 0 := by
  have words := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact words.1
  · exact words.2.1
  · exact words.2.2.1
  · exact words.2.2.2.1
  · exact words.2.2.2.2.1
  · exact words.2.2.2.2.2.1
  · exact words.2.2.2.2.2.2

theorem zero_bytes {s t : RamState} (v : Variant)
    (effect : (Stages.zeroEffect v s).Holds s t)
    (readable : MemReadable t (rspOf s + BitVec.ofNat 64 v.tail) 56) :
    (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
      t.external ⟨Array.replicate 56 0⟩ := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi : i.val < 56 := i.isLt
  have allocated : ∀ k < 8,
      (t.external[rspOf s + BitVec.ofNat 64 (v.tail+8*(i.val/8)) + BitVec.ofNat 64 k]?).isSome := by
    intro k hk
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using readable.mem (8*(i.val/8)+k) (by omega)
  have bytes := Bytes.of_memLoad (n := 64) allocated
  rw [zero_words v effect (i.val/8) (by omega)] at bytes
  have byte := bytes (i.val%8) (by omega)
  have address : rspOf s + BitVec.ofNat 64 (v.tail+8*(i.val/8)) + BitVec.ofNat 64 (i.val%8) =
      rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 i.val := by
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address, show storedByte (0 : BitVec 64) (i.val%8) = 0 from by simp [storedByte]] at byte
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.getElem_eq_getElem_data,
    Array.getElem_replicate] using byte


theorem length_observations {s t : RamState} {message : ByteArray} (v : Variant)
    (effect : (Stages.lengthEffect v s).Holds s t)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue v.blocksReg = BitVec.ofNat 64 (message.size / 64)) :
    t.regValue v.lengthReg = bswap64 (BitVec.ofNat 64 (8*message.size)) ∧
    memLoad t.external (rspOf s + BitVec.ofNat 64 (v.tail+56)) 64 =
      bswap64 (BitVec.ofNat 64 (8*message.size)) := by
  have r32 : (.reg v.lengthIndex : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    simp only [Variant.lengthIndex, read_regIndex]
    rw [remainder]
    exact BitVec.setWidth_ofNat_of_le (by decide) _
  have word : bswap64 (((.reg v.lengthIndex : Operand 32).read s <<< 3).setWidth 64 |||
      ((.reg v.blocksIndex : Operand 64).read s <<< 9)) = bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    rw [r32, show (.reg v.blocksIndex : Operand 64).read s = BitVec.ofNat 64 (message.size/64) from by simpa only [Variant.blocksIndex, read_regIndex, BitVec.setWidth_eq] using blocks,
      tail_shift_or_blocks]
  have writes := effect.writes
  simp only [Stages.lengthEffect, Write.AllHold, Variant.lengthIndex, Variant.blocksIndex,
    read_regIndex, BitVec.setWidth_eq] at writes word
  exact ⟨writes.2.1.trans word, writes.2.2.trans word⟩

theorem length_bytes {s t : RamState} {message : ByteArray} (v : Variant)
    (effect : (Stages.lengthEffect v s).Holds s t)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue v.blocksReg = BitVec.ofNat 64 (message.size / 64))
    (readable : MemReadable t (rspOf s + BitVec.ofNat 64 (v.tail+56)) 8) :
    (⟨(rspOf s + BitVec.ofNat 64 (v.tail+56)).toNat,8⟩ : MemoryRegion).HasBytes
      t.external (Hkdf.Proofs.NIST.Encoding.natToOctets 8 (8*message.size)) := by
  refine ⟨Hkdf.Proofs.Common.Encoding.natToOctets_size _ _, ?_⟩
  intro i
  have hi : i.val < 8 := by simpa only [Hkdf.Proofs.Common.Encoding.natToOctets_size] using i.isLt
  have bytes := Bytes.of_memLoad (n := 64) readable.mem
  rw [(length_observations v effect remainder blocks).2] at bytes
  have byte := bytes i.val hi
  rw [bswap64_ofNat_storedByte _ hi] at byte
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte

theorem length_tail_bytes {s t : RamState} {message : ByteArray} (v : Variant)
    (effect : (Stages.lengthEffect v s).Holds s t)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue v.blocksReg = BitVec.ofNat 64 (message.size / 64))
    (prefixBytes : (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message))
    (readable : MemReadable t (rspOf s + BitVec.ofNat 64 (v.tail+56)) 8) :
    (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes t.external
      (if message.size % 64 < 56 then tailFirst message else tailLast message) := by
  have prefixAfter : (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,56⟩ : MemoryRegion).HasBytes
      t.external (finalPrefix message) := by
    refine ⟨prefixBytes.1, fun i => ?_⟩
    apply Eq.trans (effect.agrees.byte ?_) (prefixBytes.2 i)
    intro c hc covered
    simp only [Stages.lengthEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, he⟩ := covered
    have hi : i.val < 56 := by have := i.isLt; have size := prefixBytes.1; change _ = 56 at size; omega
    have apart := RangeApart.offsets (rspOf s + BitVec.ofNat 64 v.tail)
      (a := 56) (len := 8) (b := 0) (count := 56)
      (by decide) (by decide) (.inr (by decide))
    apply apart j hj i.val hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc,
      BitVec.add_zero] using he.symm
  have suffix := length_bytes v effect remainder blocks readable
  have block : (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes t.external
      (finalBlock message) := by
    have prefixSize : (finalPrefix message).size = 56 := prefixBytes.1
    have blockSize : (finalBlock message).size = 64 := by
      simp only [finalBlock, ByteArray.size_append, prefixSize,
        Hkdf.Proofs.Common.Encoding.natToOctets_size]
    refine ⟨blockSize, fun i => ?_⟩
    have hi : i.val < 64 := by have := i.isLt; omega
    have hi' : i.val < (finalPrefix message ++
        Hkdf.Proofs.NIST.Encoding.natToOctets 8 (8*message.size)).size := by
      simpa only [finalBlock] using i.isLt
    change t.external[BitVec.ofNat 64 ((rspOf s + BitVec.ofNat 64 v.tail).toNat+i.val)]? =
      some ((finalPrefix message ++
        Hkdf.Proofs.NIST.Encoding.natToOctets 8 (8*message.size))[i.val]'hi')
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    by_cases low : i.val < 56
    · rw [ByteArray.getElem_append_left (by omega)]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        prefixAfter.2 ⟨i.val, by omega⟩
    · rw [ByteArray.getElem_append_right (by omega)]
      have byte := suffix.2 ⟨i.val-56, by simpa only [Hkdf.Proofs.Common.Encoding.natToOctets_size] using (show i.val-56 < 8 by omega)⟩
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      have address : rspOf s + BitVec.ofNat 64 (v.tail+56) + BitVec.ofNat 64 (i.val-56) =
          rspOf s + BitVec.ofNat 64 v.tail + BitVec.ofNat 64 i.val := by
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      simp only [BitVec.ofNat_add] at address
      rw [address] at byte
      simpa only [prefixSize] using byte
  by_cases small : message.size % 64 < 56
  · simpa only [finalBlock,
      finalPrefix, tailFirst, small, ite_true] using block
  · simpa only [finalBlock,
      finalPrefix, tailLast, small, ite_false] using block

theorem copy_words {s t : RamState} (v : Variant) (last : Bool)
    (effect : (Stages.copyEffect v last s).Holds s t)
    (highword : last = true → s.regValue v.lengthReg =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+56)) 64) :
    ∀ j < 8, memLoad t.external (rspOf s + BitVec.ofNat 64 (v.scratch+8*j)) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+8*j)) 64 := by
  intro j hj
  have member : j ∈ ([0,1,2,3,4,5,6,7] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have word := Write.allHold_iff.mp effect.writes
    (⟨(.mem (rspOf s + BitVec.ofNat 64 (v.scratch+8*j)) : Operand 64),
      if last && j == 7 then s.regValue v.lengthReg
      else memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+8*j)) 64⟩)
    (List.mem_append_right _ (List.mem_map_of_mem member))
  change memLoad t.external (rspOf s + BitVec.ofNat 64 (v.scratch+8*j)) 64 =
      (if last && j == 7 then s.regValue v.lengthReg
       else memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+8*j)) 64) at word
  rw [word]
  split
  · rename_i hit
    simp only [Bool.and_eq_true, beq_iff_eq] at hit
    rcases hit with ⟨hLast, rfl⟩
    exact highword hLast
  · rfl

theorem copy_bytes {s t : RamState} {block : ByteArray} (v : Variant) (last : Bool)
    (effect : (Stages.copyEffect v last s).Holds s t)
    (source : (⟨(rspOf s + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes
      s.external block)
    (readable : MemReadable t (rspOf s + BitVec.ofNat 64 v.scratch) 64)
    (highword : last = true → s.regValue v.lengthReg =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+56)) 64) :
    (⟨(rspOf s + BitVec.ofNat 64 v.scratch).toNat,64⟩ : MemoryRegion).HasBytes
      t.external block := by
  refine ⟨source.1, ?_⟩
  intro i
  have hi : i.val < 64 := by have bound := i.isLt; have size : block.size = 64 := source.1; omega
  have word := copy_words v last effect highword (i.val/8) (by omega)
  have equal := memByte_of_memLoad_eq word (i.val%8) (by omega)
  have address (offset : Nat) :
      rspOf s + BitVec.ofNat 64 (offset+8*(i.val/8)) + BitVec.ofNat 64 (i.val%8) =
        rspOf s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i.val := by
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address, address] at equal
  have stored := source.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at stored ⊢
  have present := readable.mem i.val hi
  obtain ⟨byte, hbyte⟩ := Option.isSome_iff_exists.mp present
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0 at equal
  rw [stored, hbyte] at equal
  simp only [Option.getD_some] at equal
  rw [hbyte, equal]

end Hkdf.Proofs.Common.StreamPadding.Execution
