import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Length
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites
import Hkdf.Proofs.Common.StreamPadding.Mathematics

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Inner

open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Instructions Hkdf.Proofs.Common.StreamPadding
open Prelude X86 X86.Machine X86Proofs

theorem length_components (s : RamState) :
    (lengthEffect s).components =
      [.reg 13, .reg 15, .mem (stackPtr s + 136) 8, .mem (stackPtr s + 72) 8, .flags, .rip] := by
  simp [lengthEffect, Effect.components, Write.component, Operand.component]
  rfl

theorem length_footprint (s : RamState) :
    StackWrites (lengthEffect s).components (stackPtr s) [(136, 8), (72, 8)] := by
  intro c member a covered
  rw [length_components] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  · exact ⟨(136, 8), by simp, covered⟩
  · exact ⟨(72, 8), by simp, covered⟩

private theorem length_word {s : RamState} {message : ByteArray}
    (rem : s.regValue .r15 = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue .r13 = BitVec.ofNat 64 (message.size / 64)) :
    lengthWord s = bswap64 (BitVec.ofNat 64 (8 * message.size)) := by
  unfold lengthWord
  rw [← Operand.setWidth_read_reg64]
  change bswap64 (((s.regValue .r15).setWidth 32 <<< 3).setWidth 64 |||
    (s.regValue .r13 <<< 9)) = _
  rw [rem, blocks, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), tail_shift_or_blocks]

theorem length_slots {s t : RamState} {message : ByteArray}
    (effect : (lengthEffect s).Holds s t)
    (rem : s.regValue .r15 = BitVec.ofNat 64 (message.size % 64))
    (blocks : s.regValue .r13 = BitVec.ofNat 64 (message.size / 64)) :
    memLoad t.external (stackPtr s + 136) 64 = bswap64 (BitVec.ofNat 64 (8 * message.size)) ∧
      memLoad t.external (stackPtr s + 72) 64 = memLoad t.external (stackPtr s + 136) 64 :=
  ⟨effect.writes.2.2.1.trans (length_word rem blocks),
    effect.writes.2.2.2.trans effect.writes.2.2.1.symm⟩

theorem block_bytes {s t : RamState} {message : ByteArray}
    (prefixBytes : (⟨(stackPtr s + 80).toNat, 56⟩ : MemoryRegion).HasBytes
      s.external (finalPrefix message))
    (effect : (lengthEffect s).Holds s t)
    (readable : MemReadable t (stackPtr s + 136) 8)
    (encoded : memLoad t.external (stackPtr s + 136) 64 =
      bswap64 (BitVec.ofNat 64 (8 * message.size))) :
    (⟨(stackPtr s + 80).toNat, 64⟩ : MemoryRegion).HasBytes t.external (finalBlock message) := by
  have prefixSize : (finalPrefix message).size = 56 := prefixBytes.1
  have afterPrefix : (Component.mem (stackPtr s + BitVec.ofNat 64 80) 56).Agrees s t := by
    apply (length_footprint s).agrees effect.agrees (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  have blockSize : (finalBlock message).size = 64 := by
    simp only [finalBlock, ByteArray.size_append, prefixSize, Hkdf.Proofs.Common.Encoding.natToOctets_size]
  have bytes := Bytes.of_memLoad (n := 64) readable.mem
  rw [encoded] at bytes
  refine ⟨blockSize, fun i ↦ ?_⟩
  have hi : i.val < 64 := by have := i.isLt; omega
  have hi' : i.val < (finalPrefix message ++
      Hkdf.Proofs.NIST.Encoding.natToOctets 8 (8 * message.size)).size := i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr s + 80).toNat + i.val)]? =
    some ((finalPrefix message ++ Hkdf.Proofs.NIST.Encoding.natToOctets 8 (8 * message.size))[i.val]'hi')
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases low : i.val < 56
  · rw [ByteArray.getElem_append_left (by omega)]
    have same := afterPrefix i.val low
    have byte := prefixBytes.2 ⟨i.val, by omega⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    exact same.trans byte
  · let j := i.val - 56
    have hj : j < 8 := by dsimp [j]; omega
    rw [ByteArray.getElem_append_right (by omega)]
    have byte := bytes j hj
    rw [bswap64_ofNat_storedByte _ hj] at byte
    have address : stackPtr s + 136 + BitVec.ofNat 64 j =
        stackPtr s + 80 + BitVec.ofNat 64 i.val := by
      change stackPtr s + BitVec.ofNat 64 136 + BitVec.ofNat 64 j =
        stackPtr s + BitVec.ofNat 64 80 + BitVec.ofNat 64 i.val
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 2
      dsimp [j]
      omega
    rw [address] at byte
    simpa only [prefixSize, j] using byte

end Hkdf.Proofs.NewExpand.Expand.Finalize.Inner
