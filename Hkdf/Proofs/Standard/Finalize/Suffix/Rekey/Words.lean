import Hkdf.Proofs.Key.Hash.Initialize.Payload
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Stages
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekeyed

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Words

open Prelude X86 X86.Machine X86Proofs Hkdf.Spec.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

structure InitialRegisters (s : RamState) : Prop where
  r13 : s.regValue .r13 = 0xbb67ae856a09e667
  r12 : s.regValue .r12 = 0xa54ff53a3c6ef372
  r15 : s.regValue .r15 = 0x9b05688c510e527f
  r14 : s.regValue .r14 = 0x5be0cd191f83d9ab

theorem InitialRegisters.of_saved {s t : RamState} (h : InitialRegisters s)
    (regs : CalleeSavedRegistersUnchanged s t) : InitialRegisters t :=
  ⟨(regs .r13 (by simp)).trans h.r13, (regs .r12 (by simp)).trans h.r12,
    (regs .r15 (by simp)).trans h.r15, (regs .r14 (by simp)).trans h.r14⟩

private theorem word_bytes {s : RamState} {base : BitVec 64} {len offset : Nat}
    (allocated : ∀ i < len, (s.external[base + BitVec.ofNat 64 i]?).isSome)
    (within : offset + 8 ≤ len) :
    Bytes s.external (base + BitVec.ofNat 64 offset) 8
      (storedByte (memLoad s.external (base + BitVec.ofNat 64 offset) 64)) := by
  apply Bytes.of_memLoad (n := 64)
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact allocated (offset + i) (by omega)

private theorem setup_payload {t : RamState} {base : BitVec 64}
    (readable : MemReadable t base 40)
    (w0 : memLoad t.external base 64 = 0xbb67ae856a09e667)
    (w1 : memLoad t.external (base + 8) 64 = 0xa54ff53a3c6ef372)
    (w2 : memLoad t.external (base + 16) 64 = 0x9b05688c510e527f)
    (w3 : memLoad t.external (base + 24) 64 = 0x5be0cd191f83d9ab)
    (count : memLoad t.external (base + 32) 64 = 1) :
    HashStateAt t base initialHash ∧ loadBytes t.external (base + 32) 8 = .ok 1 := by
  refine ⟨Hkdf.Proofs.Key.Hash.Initialize.hashStateAt_initialHash_of_packedWords
    ⟨by have low := readable.low; omega, fun i hi => readable.mem i (by omega)⟩ ?_, ?_⟩
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getElem!_cons_zero] using w0
    · exact w1
    · exact w2
    · exact w3
  · have bytes := word_bytes (offset := 32) readable.mem (by decide)
    change Bytes t.external (base + 32) 8 (storedByte (memLoad t.external (base + 32) 64)) at bytes
    rw [count] at bytes
    exact bytes.loadBytes64

theorem setup_false_words {s t : RamState} (effect : (Stages.setupEffect false s).Holds s t)
    (readable : MemReadable t (rspOf s + 248) 40) :
    HashStateAt t (rspOf s + 248) initialHash ∧
      loadBytes t.external (rspOf s + 280) 8 = .ok 1 ∧ InitialRegisters t := by
  rcases effect.writes with ⟨r14, r15, r12, r13, w3, w2, w1, w0, count, _⟩
  obtain ⟨hash, blocks⟩ := setup_payload readable w0
    (by rw [BitVec.add_assoc, show (248 : BitVec 64) + 8 = 256 by decide]; exact w1)
    (by rw [BitVec.add_assoc, show (248 : BitVec 64) + 16 = 264 by decide]; exact w2)
    (by rw [BitVec.add_assoc, show (248 : BitVec 64) + 24 = 272 by decide]; exact w3)
    (by rw [BitVec.add_assoc, show (248 : BitVec 64) + 32 = 280 by decide]; exact count)
  rw [BitVec.add_assoc, show (248 : BitVec 64) + 32 = 280 by decide] at blocks
  exact ⟨hash, blocks, ⟨r13, r12, r15, r14⟩⟩

theorem setup_true_words {s t : RamState} (effect : (Stages.setupEffect true s).Holds s t)
    (readable : MemReadable t (rspOf s + 8) 40) (regs : InitialRegisters s) :
    HashStateAt t (rspOf s + 8) initialHash ∧ loadBytes t.external (rspOf s + 40) 8 = .ok 1 := by
  rcases effect.writes with ⟨w3, w2, w1, w0, count, _⟩
  obtain ⟨hash, blocks⟩ := setup_payload readable
    ((show memLoad t.external (rspOf s + 8) 64 = s.regValue .r13 from w0).trans regs.r13)
    (by
      rw [BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 by decide]
      exact (show _ = s.regValue .r12 from w1).trans regs.r12)
    (by
      rw [BitVec.add_assoc, show (8 : BitVec 64) + 16 = 24 by decide]
      exact (show _ = s.regValue .r15 from w2).trans regs.r15)
    (by
      rw [BitVec.add_assoc, show (8 : BitVec 64) + 24 = 32 by decide]
      exact (show _ = s.regValue .r14 from w3).trans regs.r14)
    (by rw [BitVec.add_assoc, show (8 : BitVec 64) + 32 = 40 by decide]; exact count)
  rw [BitVec.add_assoc, show (8 : BitVec 64) + 32 = 40 by decide] at blocks
  exact ⟨hash, blocks⟩

private theorem copy_word {s t : RamState} (effect : (Stages.copyEffect s).Holds s t)
    (outer : Bool) (j : Nat) (hj : j < 5) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 ((if outer then 328 else 288) + 8 * j)) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 ((if outer then 8 else 248) + 8 * j)) 64 := by
  let write : Write :=
    ⟨(.mem (rspOf s + BitVec.ofNat 64 ((if outer then 328 else 288) + 8 * j)) : Operand 64),
      memLoad s.external (rspOf s + BitVec.ofNat 64 ((if outer then 8 else 248) + 8 * j)) 64⟩
  have member : write ∈ (Stages.copyEffect s).writes := by
    change write ∈ _ ++ _
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨j, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · cases outer
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
  exact (Write.allHold_iff.mp effect.writes) write member

private theorem copy_payload {s t : RamState} {src dest : BitVec 64} {hash : Array UInt32}
    (input : HashStateAt s src hash) (count : loadBytes s.external (src + 32) 8 = .ok 1)
    (allocated : ∀ i < 40, (t.external[dest + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 5, memLoad t.external (dest + BitVec.ofNat 64 (8 * j)) 64 =
      memLoad s.external (src + BitVec.ofNat 64 (8 * j)) 64) :
    HashStateAt t dest hash ∧ loadBytes t.external (dest + 32) 8 = .ok 1 := by
  have inputAllocated : ∀ i < 40, (s.external[src + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    by_cases h : i < 32
    · have found := Memory.loadBytes_allocated (input.2 (i / 4) (by omega)) (i % 4) (by omega)
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
        show 4 * (i / 4) + i % 4 = i by omega] using found
    · have found := Memory.loadBytes_allocated count (i - 32) (by omega)
      change (s.external[src + BitVec.ofNat 64 32 + BitVec.ofNat 64 (i - 32)]?).isSome at found
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + (i - 32) = i by omega] at found
  have bytes : ∀ i < 40,
      t.external[dest + BitVec.ofNat 64 i]? = s.external[src + BitVec.ofNat 64 i]? := by
    intro i hi
    have out := word_bytes (offset := 8 * (i / 8)) allocated (by omega)
    have inp := word_bytes (offset := 8 * (i / 8)) inputAllocated (by omega)
    rw [words (i / 8) (by omega)] at out
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 8 * (i / 8) + i % 8 = i by omega] using
      (out (i % 8) (by omega)).trans (inp (i % 8) (by omega)).symm
  refine ⟨hashState_of_bytes input (fun i hi => bytes i (by omega)), ?_⟩
  have countWord := words 4 (by decide)
  change memLoad t.external (dest + 32) 64 = memLoad s.external (src + 32) 64 at countWord
  have countBytes := word_bytes (offset := 32) allocated (by decide)
  change Bytes t.external (dest + 32) 8 (storedByte (memLoad t.external (dest + 32) 64)) at countBytes
  rw [countWord, Memory.memLoad_of_loadBytes64 count] at countBytes
  exact countBytes.loadBytes64

theorem copy_words {s t : RamState} {key : ByteArray}
    (effect : (Stages.copyEffect s).Holds s t) (readable : MemReadable t (rspOf s + 288) 80)
    (innerHash : HashStateAt s (rspOf s + 248)
      (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x36)))
    (innerBlocks : loadBytes s.external (rspOf s + 280) 8 = .ok 1)
    (outerHash : HashStateAt s (rspOf s + 8)
      (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c)))
    (outerBlocks : loadBytes s.external (rspOf s + 40) 8 = .ok 1) :
    Suffix.RekeyedAt t (rspOf s + 288) key := by
  obtain ⟨inner, innerCount⟩ := copy_payload (dest := rspOf s + 288) innerHash
    (by rw [BitVec.add_assoc, show (248 : BitVec 64) + 32 = 280 by decide]; exact innerBlocks)
    (fun i hi => readable.mem i (by omega)) (fun j hj => by
      simpa only [Bool.false_eq_true, ite_false, BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using copy_word effect false j hj)
  obtain ⟨outer, outerCount⟩ := copy_payload (dest := rspOf s + 328) outerHash
    (by rw [BitVec.add_assoc, show (8 : BitVec 64) + 32 = 40 by decide]; exact outerBlocks)
    (fun i hi => by
      have found := readable.mem (40 + i) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at found
      change (t.external[(rspOf s + 288 + 40) + BitVec.ofNat 64 i]?).isSome at found
      rwa [BitVec.add_assoc (rspOf s) 288 40, show (288 : BitVec 64) + 40 = 328 by decide] at found) (fun j hj => by
      simpa only [ite_true, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
        using copy_word effect true j hj)
  refine ⟨inner, innerCount, ?_, ?_⟩
  · rw [BitVec.add_assoc, show (288 : BitVec 64) + 40 = 328 by decide]
    exact outer
  · have addr : rspOf s + 288 + 72 = rspOf s + 328 + 32 := by
      rw [BitVec.add_assoc, BitVec.add_assoc, show (288 : BitVec 64) + 72 = 328 + 32 by decide]
    exact addr.symm ▸ outerCount

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Words
