import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine

inductive StackImage where
  | original
  | copy (previous source : StackImage) (dst src : Fin 256) (wide : Bool)

namespace StackImage

private def width (wide : Bool) : Nat := if wide then 64 else 32

def memory (sp : BitVec 64) (initial : Ram) : StackImage → Ram
  | .original => initial
  | .copy previous source dst src wide =>
    memStore (previous.memory sp initial) (sp + BitVec.ofNat 64 dst)
      (memLoad (source.memory sp initial) (sp + BitVec.ofNat 64 src) (width wide))

def origin : StackImage → Nat → Nat
  | .original, i => i
  | .copy previous source dst src wide, i =>
    if dst.val ≤ i ∧ i < dst.val + width wide / 8 then
      source.origin (src.val + (i - dst.val))
    else previous.origin i

theorem byte_origin (img : StackImage) (sp : BitVec 64) (initial : Ram)
    (i : Nat) (hi : i < 512) :
    memByte (img.memory sp initial) (sp + BitVec.ofNat 64 i) =
      memByte initial (sp + BitVec.ofNat 64 (img.origin i)) := by
  induction img generalizing i with
  | original => rfl
  | copy previous source dst src wide prevIH srcIH =>
    have hw : width wide / 8 ≤ 8 := by cases wide <;> decide
    simp only [memory, origin]
    split
    next h =>
      obtain ⟨hle, hlt⟩ := h
      have hj : i - dst.val < width wide / 8 := by omega
      have ha : sp + BitVec.ofNat 64 i =
          sp + BitVec.ofNat 64 dst + BitVec.ofNat 64 (i - dst.val) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hle]
      rw [ha, memByte]
      simp only [PhysicalMemory.read]
      rw [memStore_getElem?_self_of_le _ _ _ (by omega) _ hj]
      simp only [Option.getD_some, storedByte_memLoad _ _ _ hj, BitVec.add_assoc,
        ← BitVec.ofNat_add]
      exact srcIH _ (by have := src.isLt; omega)
    next h =>
      have ha : ∀ j, j < width wide / 8 →
          sp + BitVec.ofNat 64 dst + BitVec.ofNat 64 j ≠ sp + BitVec.ofNat 64 i := by
        intro j hj he
        rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
        have heq := add_ofNat_inj sp (i := i) (j := dst.val + j) (by omega)
          (by have := dst.isLt; omega) he
        omega
      change ((memStore _ _ _)[sp + BitVec.ofNat 64 i]?).getD 0 = _
      rw [memStore_getElem?_of_ne _ _ _ _ ha]
      exact prevIH i hi

private def endOffset : StackImage → Nat
  | .original => 0
  | .copy previous _ dst _ wide => max previous.endOffset (dst.val + width wide / 8)

private theorem frame (img : StackImage) (sp : BitVec 64) (initial : Ram)
    {bound : Nat} (hbound : img.endOffset ≤ bound) (low : sp.toNat + bound < 2^64) :
    RamWriteFrame initial (img.memory sp initial) [⟨sp.toNat, bound⟩] := by
  induction img with
  | original => exact .refl _ _
  | copy previous source dst src wide prevIH _ =>
    obtain ⟨hp, hd⟩ := Nat.max_le.mp hbound
    apply (prevIH hp).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have he : (sp + BitVec.ofNat 64 dst.val).toNat = sp.toNat + dst.val := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dst.isLt; omega),
        Nat.mod_eq_of_lt (by omega)]
    simp only [InRegion, he]
    omega

end StackImage

def rearranged : StackImage :=
  let m0 := StackImage.original
  let m1 := m0.copy m0 4 160 false
  let m2 := m1.copy m0 7 163 false
  let m3 := m2.copy m2 72 171 true
  let m4 := m3.copy m3 80 179 true
  let m5 := m4.copy m4 88 187 true
  let m6 := m5.copy m5 96 195 true
  let m7 := m6.copy m6 104 203 true
  let m8 := m7.copy m7 112 211 true
  let m9 := m8.copy m8 118 217 true
  let m10 := m9.copy m2 11 167 false
  let m11 := m10.copy m10 15 72 true
  let m12 := m11.copy m10 23 80 true
  let m13 := m12.copy m12 31 88 true
  let m14 := m13.copy m13 39 96 true
  let m15 := m14.copy m14 47 104 true
  let m16 := m15.copy m15 55 112 true
  let m17 := m16.copy m16 61 118 true
  m17

private theorem rearranged_origin : ∀ i < 65, rearranged.origin (4 + i) = 160 + i := by
  decide +kernel

theorem rearranged_bytes (sp : BitVec 64) (initial : Ram) (i : Nat) (hi : i < 65) :
    memByte (rearranged.memory sp initial) (sp + BitVec.ofNat 64 (4 + i)) =
      memByte initial (sp + BitVec.ofNat 64 (160 + i)) := by
  rw [StackImage.byte_origin _ _ _ _ (by omega), rearranged_origin i hi]

theorem rearranged_frame (sp : BitVec 64) (initial : Ram) (low : sp.toNat + 126 < 2^64) :
    RamWriteFrame initial (rearranged.memory sp initial) [⟨sp.toNat, 126⟩] :=
  StackImage.frame _ _ _ (by decide +kernel) low

def affineMemory (sp : BitVec 64) (m : Ram) : Ram :=
  memStore (rearranged.memory sp m) (sp - 8) (0x1064f4 : BitVec 64)

set_option maxRecDepth 2048 in
theorem affineMemory_bytes (sp : BitVec 64) (m : Ram) (i : Nat) (hi : i < 65) :
    memByte (affineMemory sp m) (sp + 4 + BitVec.ofNat 64 i) =
      memByte m (sp + 160 + BitVec.ofNat 64 i) := by
  have apart : RangeApart (sp - 8) 8 (sp + 4) 65 :=
    RangeApart.of_offsets (x := sp) (c := 0 - 8) (d := 4) (addr_sub _ _) rfl (by decide)
  have keep : memByte (affineMemory sp m) (sp + 4 + BitVec.ofNat 64 i) =
      memByte (rearranged.memory sp m) (sp + 4 + BitVec.ofNat 64 i) :=
    congrArg (fun x : Option UInt8 => x.getD 0)
      (memStore_getElem?_of_ne (rearranged.memory sp m) (sp - 8) (0x1064f4 : BitVec 64)
        (sp + 4 + BitVec.ofNat 64 i) (fun j hj => apart j hj i hi))
  rw [keep]
  have add (k : Nat) : sp + BitVec.ofNat 64 k + BitVec.ofNat 64 i =
      sp + BitVec.ofNat 64 (k + i) := by rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact (congrArg (memByte (rearranged.memory sp m)) (add 4)).trans
    ((rearranged_bytes sp m i hi).trans (congrArg (memByte m) (add 160)).symm)

end K256.Proofs.Sec1.Parser.Packing
