import AesGcm.Proofs.AES16.KeySchedule.Generation.State
import X86Proofs.Program.ReadWrite.Bytes

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine Fixslice16
open AesGcm.Proofs.Machine.Runtime

theorem rcon_store_load (mem : Ram) (base : BitVec 64) :
    memLoad (memStore mem base (memLoad mem base 8 ^^^ (0x80 : BitVec 8))) base 16 =
      memLoad mem base 16 ^^^ (0x80 : BitVec 16) := by
  have hbyte (m : Ram) (a : BitVec 64) : memByte m a = storedByte (memLoad m a 8) 0 := by
    symm
    simpa only [BitVec.add_zero] using storedByte_memLoad m a (n := 8) 0 (by decide)
  have hmask : ∀ i : Fin 2, storedByte (0x80 : BitVec 16) i.val =
      if i.val = 0 then (0x80 : UInt8) else 0 := by decide +kernel
  have hdiff : ∀ i : Fin 2, i.val ≠ 0 →
      1 ≤ (BitVec.ofNat 64 i.val).toNat ∧
      1 ≤ ((0 : BitVec 64) - BitVec.ofNat 64 i.val).toNat := by decide +kernel
  apply memLoad_eq_of_memByte (by decide)
  intro i hi
  rw [storedByte_xor, storedByte_memLoad mem base i hi, hmask ⟨i, by omega⟩]
  by_cases hi0 : i = 0
  · subst i
    simp only [ite_true, BitVec.add_zero]
    rw [hbyte, memLoad_memStore (n := 8) mem base (by decide) (by decide) _, storedByte_xor,
      storedByte_memLoad mem base (n := 8) 0 (by decide), BitVec.add_zero]
    rfl
  · rw [ite_eq_right hi0, UInt8.xor_zero, hbyte]
    have hap : RangeApart base 1 (base + BitVec.ofNat 64 i) 1 :=
      RangeApart.of_offsets (x := base) (c := 0) (d := BitVec.ofNat 64 i)
        (BitVec.add_zero base).symm rfl (by
          simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using hdiff ⟨i, by omega⟩ hi0)
    rw [memLoad_memStore_of_rangeApart mem base (base + BitVec.ofNat 64 i)
      (memLoad mem base 8 ^^^ (0x80 : BitVec 8)) 8 hap,
      storedByte_memLoad mem (base + BitVec.ofNat 64 i) (n := 8) 0 (by decide), BitVec.add_zero]

theorem rcon_store_words (mem : Ram) (base : BitVec 64) (x : Planes16)
    (h : WordsAt mem base 16 (Vector.ofFn x)) (k : Fin 8) :
    WordsAt (memStore mem (base + BitVec.ofNat 64 (2 * k.val))
      (memLoad mem (base + BitVec.ofNat 64 (2 * k.val)) 8 ^^^ (0x80 : BitVec 8)))
      base 16 (Vector.ofFn fun p ↦ x p ^^^ if p = k then (0x80 : BitVec 16) else 0) := by
  have hdiff : ∀ k p : Fin 8, k ≠ p →
      1 ≤ (BitVec.ofNat 64 (2 * p.val) - BitVec.ofNat 64 (2 * k.val)).toNat ∧
      2 ≤ (BitVec.ofNat 64 (2 * k.val) - BitVec.ofNat 64 (2 * p.val)).toNat := by
    decide +kernel
  intro p hp
  simp only [Vector.getElem_ofFn]
  have hv := h p hp
  simp only [Vector.getElem_ofFn] at hv
  by_cases hpk : p = k.val
  · subst p
    have hk : (⟨k.val, hp⟩ : Fin 8) = k := Fin.ext rfl
    simp only [hk, ite_true]
    change memLoad (memStore mem (wordAddr base 16 k.val)
      (memLoad mem (wordAddr base 16 k.val) 8 ^^^ (0x80 : BitVec 8))) _ 16 = _
    rw [rcon_store_load, hv]
  · have hfin : (⟨p, hp⟩ : Fin 8) ≠ k := fun heq ↦ hpk (congrArg Fin.val heq)
    simp only [ite_eq_right hfin, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
    have hap : RangeApart (base + BitVec.ofNat 64 (2 * k.val)) 1
        (wordAddr base 16 p) 2 :=
      RangeApart.of_offsets (x := base) (c := BitVec.ofNat 64 (2 * k.val))
        (d := BitVec.ofNat 64 (2 * p)) rfl rfl
        (hdiff k ⟨p, hp⟩ (fun heq ↦ hpk (congrArg Fin.val heq).symm))
    rw [memLoad_memStore_of_rangeApart mem (base + BitVec.ofNat 64 (2 * k.val))
      (wordAddr base 16 p) _ 16 hap]
    exact hv

theorem subBytesNots_store_words (mem : Ram) (base : BitVec 64)
    (x : Planes16) (h : WordsAt mem base 16 (Vector.ofFn x))
    (hbound : base.toNat + 16 ≤ 2 ^ 64) :
    let m0 := memStore mem (wordAddr base 16 0) (~~~(memLoad mem (wordAddr base 16 0) 16))
    let m1 := memStore m0 (wordAddr base 16 1) (~~~(memLoad m0 (wordAddr base 16 1) 16))
    let m2 := memStore m1 (wordAddr base 16 5) (~~~(memLoad m1 (wordAddr base 16 5) 16))
    let m3 := memStore m2 (wordAddr base 16 6) (~~~(memLoad m2 (wordAddr base 16 6) 16))
    WordsAt m3 base 16 (Vector.ofFn (Fixslice16.subBytesNots x)) := by
  let m0 := memStore mem (wordAddr base 16 0) (~~~(memLoad mem (wordAddr base 16 0) 16))
  let m1 := memStore m0 (wordAddr base 16 1) (~~~(memLoad m0 (wordAddr base 16 1) 16))
  let m2 := memStore m1 (wordAddr base 16 5) (~~~(memLoad m1 (wordAddr base 16 5) 16))
  let m3 := memStore m2 (wordAddr base 16 6) (~~~(memLoad m2 (wordAddr base 16 6) 16))
  let v0 := (Vector.ofFn x).set 0 (~~~(memLoad mem (wordAddr base 16 0) 16)) (by decide)
  let v1 := v0.set 1 (~~~(memLoad m0 (wordAddr base 16 1) 16)) (by decide)
  let v2 := v1.set 5 (~~~(memLoad m1 (wordAddr base 16 5) 16)) (by decide)
  let v3 := v2.set 6 (~~~(memLoad m2 (wordAddr base 16 6) 16)) (by decide)
  have h0 : WordsAt m0 base 16 v0 :=
    h.write_set (by decide) _ (by decide) (by decide) (by decide) hbound
  have h1 : WordsAt m1 base 16 v1 :=
    h0.write_set (by decide) _ (by decide) (by decide) (by decide) hbound
  have h2 : WordsAt m2 base 16 v2 :=
    h1.write_set (by decide) _ (by decide) (by decide) (by decide) hbound
  have h3 : WordsAt m3 base 16 v3 :=
    h2.write_set (by decide) _ (by decide) (by decide) (by decide) hbound
  have hx0 : memLoad mem (wordAddr base 16 0) 16 = x 0 := by
    simpa using h 0 (by decide)
  have hx1 : memLoad m0 (wordAddr base 16 1) 16 = x 1 := by
    simpa [v0] using h0 1 (by decide)
  have hx5 : memLoad m1 (wordAddr base 16 5) 16 = x 5 := by
    simpa [v1, v0] using h1 5 (by decide)
  have hx6 : memLoad m2 (wordAddr base 16 6) 16 = x 6 := by
    simpa [v2, v1, v0] using h2 6 (by decide)
  have hv : v3 = Vector.ofFn (Fixslice16.subBytesNots x) := by
    dsimp only [v3, v2, v1, v0]
    rw [hx0, hx1, hx5, hx6]
    apply Vector.ext
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Vector.getElem_set, Vector.getElem_ofFn,
      Fixslice16.subBytesNots, Nat.reduceEqDiff, ↓reduceIte,
      or_true, or_false]
    all_goals rfl
  rw [hv] at h3
  exact h3


theorem rcon_plane_mask_source (r : Fin 10) (p : Fin 8) :
    (if ((rcon (r.val + 1))[0]).toBitVec.getLsbD p.val then (0x80 : BitVec 16) else 0) =
      if r.val < 8 then (if p.val = r.val then 0x80 else 0)
      else (if p.val = r.val - 8 then 0x80 else 0) ^^^
        (if p.val = r.val - 7 then 0x80 else 0) ^^^
        (if p.val = r.val - 5 then 0x80 else 0) ^^^
        (if p.val = r.val - 4 then 0x80 else 0) := by
  have h := congrArg (fun x : BitVec 64 ↦ projectWord x 0)
    (Machine.KeySchedule.rcon_plane_mask_source r p)
  have hm : projectWord (0xf0000000 : BitVec 64) 0 = 0x80 := by decide +kernel
  have hz : projectWord (0 : BitVec 64) 0 = 0 := by decide +kernel
  have projectMask (c : Prop) [Decidable c] :
      projectWord (if c then (0xf0000000 : BitVec 64) else 0) 0 =
        if c then (0x80 : BitVec 16) else 0 := by
    split
    · exact hm
    · exact hz
  by_cases hr : r.val < 8
  · rw [ite_eq_left hr] at h ⊢
    simpa only [projectMask] using h
  · rw [ite_eq_right hr] at h ⊢
    simpa only [projectWord_xor, projectMask] using h

def rconStore (mem : Ram) (base : BitVec 64) (i : Nat) : Ram :=
  memStore mem (base + BitVec.ofNat 64 (2 * i))
    (memLoad mem (base + BitVec.ofNat 64 (2 * i)) 8 ^^^ (0x80 : BitVec 8))

def rconStores (mem : Ram) (base : BitVec 64) (k : Fin 10) : Ram :=
  if k.val < 8 then rconStore mem base k.val else
    rconStore (rconStore (rconStore (rconStore mem base (k.val - 8))
      base (k.val - 7)) base (k.val - 5)) base (k.val - 4)

theorem rcon_words (mem : Ram) (base : BitVec 64) (x : Planes16) (k : Fin 10)
    (hx : WordsAt mem base 16 (Vector.ofFn x)) :
    WordsAt (rconStores mem base k) base 16 (Vector.ofFn fun p ↦ x p ^^^
      if ((rcon (k.val + 1))[0]).toBitVec.getLsbD p.val then (0x80 : BitVec 16) else 0) := by
  unfold rconStores
  by_cases hk : k.val < 8
  · rw [ite_eq_left hk]
    have h := rcon_store_words mem base x hx ⟨k.val, hk⟩
    change WordsAt (rconStore mem base k.val) base 16 _ at h
    have he : (Vector.ofFn fun p : Fin 8 ↦ x p ^^^
        if p = ⟨k.val, hk⟩ then (0x80 : BitVec 16) else 0) =
        Vector.ofFn (fun p ↦ x p ^^^
          if ((rcon (k.val + 1))[0]).toBitVec.getLsbD p.val then 0x80 else 0) := by
      apply Vector.ext
      intro p hp
      simp only [Vector.getElem_ofFn, rcon_plane_mask_source, hk, ↓reduceIte, Fin.ext_iff]
    rw [he] at h
    exact h
  · rw [ite_eq_right hk]
    have hklt := k.isLt
    let i0 : Fin 8 := ⟨k.val - 8, by omega⟩
    let i1 : Fin 8 := ⟨k.val - 7, by omega⟩
    let i2 : Fin 8 := ⟨k.val - 5, by omega⟩
    let i3 : Fin 8 := ⟨k.val - 4, by omega⟩
    have h0 := rcon_store_words mem base x hx i0
    have h1 := rcon_store_words _ base _ h0 i1
    have h2 := rcon_store_words _ base _ h1 i2
    have h3 := rcon_store_words _ base _ h2 i3
    change WordsAt (rconStore (rconStore (rconStore (rconStore mem base i0.val)
      base i1.val) base i2.val) base i3.val) base 16 _ at h3
    have he : (Vector.ofFn fun p : Fin 8 ↦ (((x p ^^^
        (if p = i0 then (0x80 : BitVec 16) else 0)) ^^^
        (if p = i1 then 0x80 else 0)) ^^^ (if p = i2 then 0x80 else 0)) ^^^
        (if p = i3 then 0x80 else 0)) =
        Vector.ofFn (fun p ↦ x p ^^^
          if ((rcon (k.val + 1))[0]).toBitVec.getLsbD p.val then 0x80 else 0) := by
      apply Vector.ext
      intro p hp
      simp only [Vector.getElem_ofFn, rcon_plane_mask_source, hk, ↓reduceIte,
        Fin.ext_iff, i0, i1, i2, i3, BitVec.xor_assoc]
    rw [he] at h3
    exact h3

theorem subBytesNots_subBytes_encodeStandard (x : Standards.NIST.AES.Block) :
    Fixslice16.subBytesNots (Fixslice16.subBytes (encodeStandard x)) =
      encodeStandard (Standards.NIST.AES.subBytes x) := by
  rw [encodeStandard, subBytesNots_subBytes_encode]
  apply congrArg encode
  funext j
  simp only [fromStandard, Standards.NIST.AES.subBytes, Vector.getElem_map,
    UInt8.ofBitVec_toBitVec]


end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
