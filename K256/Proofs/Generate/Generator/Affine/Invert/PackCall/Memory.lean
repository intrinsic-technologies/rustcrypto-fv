import K256.Proofs.Generate.Generator.Affine.Invert.PackCall.Block
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Affine.Invert.PackCall

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Sec1.Affine.Uncompressed (SlotState slotAddr)

def slotRegion (q : Word) : MemoryRegion := ⟨(q - 8).toNat, 40⟩

theorem pushed_frame (m : Ram) (q : Word) (w : Vector Word 4) (n : Nat) (hn : n ≤ 4)
    (low : (q - 8).toNat + 40 ≤ 2^32) :
    RamWriteFrame m (pushed m q w n hn) [slotRegion q] := by
  induction n with
  | zero => exact RamWriteFrame.refl _ _
  | succ n ih =>
    rw [pushed]
    apply (ih (by omega)).memStore
    refine ⟨_, List.mem_cons_self, ?_⟩
    have eq : (if n = 0 then q else wordAddr q 64 n) = (q - 8) + BitVec.ofNat 64 (8 + 8 * n) := by
      have addr : (if n = 0 then q else wordAddr q 64 n) = q + BitVec.ofNat 64 (8 * n) := by
        by_cases h : n = 0
        · subst n
          exact (BitVec.add_zero q).symm
        · simp only [h, ite_false, wordAddr, Nat.reduceDiv]
      rw [addr, BitVec.ofNat_add]
      bv_omega
    have ns : (BitVec.ofNat 64 (8 + 8 * n)).toNat = 8 + 8 * n := Nat.mod_eq_of_lt (by omega)
    have na : ((q - 8) + BitVec.ofNat 64 (8 + 8 * n)).toNat = (q - 8).toNat + (8 + 8 * n) := by
      rw [BitVec.toNat_add, ns, Nat.mod_eq_of_lt (by omega)]
    rw [eq]
    dsimp only [InRegion, slotRegion]
    rw [na]
    store_disch

theorem packedStore_frame (m : Ram) (q : Word) (w : Vector Word 4)
    (low : (q - 8).toNat + 40 ≤ 2^32) :
    RamWriteFrame m (packedStore m q w) [slotRegion q] := by
  have prep : RamWriteFrame m (pushed m q w 4 (by decide)) [⟨(q - 8).toNat, 40⟩] :=
    pushed_frame m q w 4 (by decide) low
  change RamWriteFrame m (memStore (pushed m q w 4 (by decide)) (q - 8) (0x10ed84 : Word))
    [⟨(q - 8).toNat, 40⟩]
  slot_state region

theorem packedStore_ret (m : Ram) (q : Word) (w : Vector Word 4) :
    memLoad (packedStore m q w) (q - 8) 64 = 0x10ed84 :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem packedStore_words {m : Ram} {q : Word} (w : Vector Word 4)
    (win : Writable Extracted.programImage m (q - 8) 208) :
    WordsAt (packedStore m q w) q 64 w := by
  have stack := SlotState.start win
  let slots (i : Nat) : Word :=
    if i = 3 then w[3] else if i = 2 then w[2] else if i = 1 then w[1] else
      if i = 0 then w[0] else memLoad m (slotAddr q i) 64
  have ready : SlotState Extracted.programImage m (packedStore m q w) q slots := by
    change SlotState _ _ (memStore (memStore (memStore (memStore (memStore m q w[0])
      (q + 8) w[1]) (q + 16) w[2]) (q + 24) w[3]) (q - 8) (0x10ed84 : Word)) _ _
    slot_state
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · rw [show wordAddr q 64 0 = q from BitVec.add_zero q]
    exact ready.load 0 (by decide)
  · exact ready.load 1 (by decide)
  · exact ready.load 2 (by decide)
  · exact ready.load 3 (by decide)

end K256.Proofs.Generate.Generator.Affine.Invert.PackCall
