import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.Region
import K256.Proofs.Common.ScalarWords

namespace K256.Proofs.Sec1

open K256.Spec.Program K256.Proofs.Common K256.Proofs.Refine Prelude X86 X86.Machine X86Proofs
open Standards.SECG.ECC

theorem coordinate_of_memory {initial : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes initial [bytes]) {off : Nat}
    (h : off + 32 ≤ bytes.size) :
    let word := scalarWord initial.external (initial.regValue .rsi + BitVec.ofNat 64 off)
    Encoding.octetsToNat (bytes.extract off (off + 32)) =
      ((word 3).toNat * 2^64 + (word 2).toNat) * 2^128 +
        (word 1).toNat * 2^64 + (word 0).toNat := by
  have hb : (registerRegion initial .rsi bytes.size).HasBytes initial.external bytes :=
    call.inputsInMemory.1.2.2
  simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    octetsToNat_extract_eq_words hb h

theorem inputWords {initial : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    WordsAt initial.external (initial.regValue .rsi) 8
      (Vector.ofFn fun i : Fin bytes.size => bytes[i.val].toBitVec) := by
  have hb : (registerRegion initial .rsi bytes.size).HasBytes initial.external bytes :=
    call.inputsInMemory.1.2.2
  intro i hi
  rw [Vector.getElem_ofFn]
  apply memLoad_eq_of_memByte (by decide)
  intro j hj
  obtain rfl : j = 0 := by omega
  have hei := congrArg (fun a : Option UInt8 => a.getD 0) (hb.2 ⟨i, hi⟩)
  simp only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hei
  simpa [wordAddr, storedByte, memByte, PhysicalMemory.read] using hei

theorem buffers {initial : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    let src := initial.regValue .rsi
    let dst := initial.regValue .rdi
    let stack := Stack.region initial publicKeyFromSec1Bytes.minStackBytes
    Readable initial.external src bytes.size ∧
    Writable Extracted.programImage initial.external dst 65 ∧ Outside [stack] dst 65 ∧
    (0 < bytes.size → Outside [stack, outputRegion publicKeyFromSec1Bytes initial] src bytes.size) := by
  let input := registerRegion initial .rsi bytes.size
  let output := outputRegion publicKeyFromSec1Bytes initial
  let stack := Stack.region initial publicKeyFromSec1Bytes.minStackBytes
  have hi : ValidInput initial input bytes := call.inputsInMemory.1
  have ho : ValidOutput initial output := call.outputInMemory rfl
  have sep : MemorySeparation [output, stack] [input] := call.separation
  have hr := Readable.of_hasBytes hi.2.2 hi.2.1
  change Readable initial.external (BitVec.ofNat 64 (initial.regValue .rsi).toNat) bytes.size at hr
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr
  have hw : Writable Extracted.programImage initial.external (initial.regValue .rdi) 65 := by
    apply Writable.of_avoids ho.2.1 ho.2.2 (sep.2 output List.mem_cons_self).1
    · exact fun x hx => Or.inl ⟨x.2, programSections_fetchByte_of_mem hx⟩
    · intro b hb
      have h := not_pageTableEntriesApart_frames hb
      exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · decide
  have os : 0 < output.size := by exact Nat.zero_lt_succ 64
  have ss : 0 < stack.size := by
    change 0 < (initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - _)
    omega
  refine ⟨hr, hw, ⟨by have := hw.readable.low; omega, ?_⟩, ?_⟩
  · intro r h
    obtain rfl := List.mem_singleton.mp h
    exact apart_of_disjoint (List.pairwise_cons.mp sep.1 |>.1 stack List.mem_cons_self) os ss
  · intro hn
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r h
    have separate (r : MemoryRegion) (hm : r ∈ [output, stack]) (hp : 0 < r.size) :=
      (apart_of_disjoint ((sep.2 r hm).2 input List.mem_cons_self) hp hn).symm
    rcases List.mem_cons.mp h with rfl | h'
    · exact separate stack (.tail _ List.mem_cons_self) ss
    · obtain rfl := List.mem_singleton.mp h'
      exact separate _ List.mem_cons_self os

end K256.Proofs.Sec1
