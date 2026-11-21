import AesGcm.Proofs.Machine.KeySchedule.Layout
import AesGcm.Proofs.AES16.KeySchedule.Expansion
import AesGcm.Proofs.AES16.KeySchedule.Columns

namespace AesGcm.Proofs.Machine.KeySchedule

open Standards.NIST.AES AesGcm.Proofs.Machine.Fixslice

theorem roundKeyBlock_initial (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (h : 4 * (round.val + 1) ≤ v.Nk) :
    roundKeyBlock v key round = Vector.ofFn (fun j : Fin 16 ↦
      key[16 * round.val + j.val]'(by
        have := j.isLt; unfold Variant.keyBytes; omega)) := by
  apply Vector.ext
  intro j hj
  simp only [roundKeyBlock, roundKey, Vector.getElem_ofFn]
  have hi : 4 * round.val + j / 4 < v.Nk := by omega
  have hw := keyExpansion_initial v key ⟨4 * round.val + j / 4, hi⟩
  have hw' := congrArg (fun w : Word ↦ w[j % 4]) hw
  simp only [Vector.getElem_ofFn] at hw'
  rw [hw']
  congr 1
  omega

theorem expansionTemp_nonboundary (v : Variant) (i : Nat) (previous : Word)
    (hv : v ≠ .aes192) (hi : i % 4 ≠ 0) : expansionTemp v i previous = previous := by
  cases v with
  | aes128 =>
    unfold expansionTemp
    change (if i % 4 = 0 then _ else if 4 > 6 ∧ i % 4 = 4 then _ else _) = previous
    simp only [hi, show ¬(4 > 6 ∧ i % 4 = 4) by omega, ↓reduceIte]
  | aes192 => exact False.elim (hv rfl)
  | aes256 =>
    have h0 : i % 8 ≠ 0 := by omega
    have h4 : i % 8 ≠ 4 := by omega
    unfold expansionTemp
    change (if i % 8 = 0 then _ else if 8 > 6 ∧ i % 8 = 4 then _ else _) = previous
    simp only [h0, show ¬(8 > 6 ∧ i % 8 = 4) from fun h ↦ h4 h.2, ↓reduceIte]

theorem keyExpansion_four_word_recurrence (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hv : v ≠ .aes192) (hstart : v.Nk ≤ 4 * round.val) :
    let w := keyExpansion v key
    let back := Vector.ofFn (fun j : Fin 4 ↦
      w[4 * round.val + j.val - v.Nk]'(by have := j.isLt; have := round.isLt; omega))
    let temp := expansionTemp v (4 * round.val)
      (w[4 * round.val - 1]'(by have := round.isLt; omega))
    roundKey v w round = #v[
      xorWord back[0] temp,
      xorWord back[1] (xorWord back[0] temp),
      xorWord back[2] (xorWord back[1] (xorWord back[0] temp)),
      xorWord back[3] (xorWord back[2] (xorWord back[1] (xorWord back[0] temp)))] := by
  have hr := round.isLt
  have h0 := keyExpansion_recurrence v key (4 * round.val) hstart (by omega)
  have h1 := keyExpansion_recurrence v key (4 * round.val + 1) (by omega) (by omega)
  have h2 := keyExpansion_recurrence v key (4 * round.val + 2) (by omega) (by omega)
  have h3 := keyExpansion_recurrence v key (4 * round.val + 3) (by omega) (by omega)
  simp only [expansionTemp_nonboundary v (4 * round.val + 1) _ hv (by omega),
    show 4 * round.val + 1 - 1 = 4 * round.val by omega, h0] at h1
  simp only [expansionTemp_nonboundary v (4 * round.val + 2) _ hv (by omega),
    show 4 * round.val + 2 - 1 = 4 * round.val + 1 by omega, h1] at h2
  simp only [expansionTemp_nonboundary v (4 * round.val + 3) _ hv (by omega),
    show 4 * round.val + 3 - 1 = 4 * round.val + 2 by omega, h2] at h3
  apply Vector.ext
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem rcon_mask_bit (i : Fin 64) :
    (0xf0000000 : BitVec 64).getLsbD i.val =
      decide (4 * (i.val / 4 % 4) + i.val / 16 = 13) := by
  decide +kernel +revert

theorem encode_rcon_byte (x : Blocks) (c : UInt8) :
    (fun p : Fin 8 ↦ encode x p ^^^
      (if c.toBitVec.getLsbD p.val then (0xf0000000 : BitVec 64) else 0)) =
      encode (fun b j ↦ if j.val = 13 then x b j ^^^ c.toBitVec else x b j) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_encode x p ⟨i, hi⟩,
    getLsbD_encode _ p ⟨i, hi⟩]
  have hm := rcon_mask_bit ⟨i, hi⟩
  simp only [BitVec.ofNat_eq_ofNat] at hm
  by_cases hj : 4 * (i / 4 % 4) + i / 16 = 13
  all_goals cases hc : c.toBitVec.getLsbD p.val
  all_goals simp only [hj, ↓reduceIte, hc, Bool.false_eq_true,
    BitVec.getLsbD_xor, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, hm, decide_true, decide_false,
    Bool.xor_false, Bool.xor_true]

theorem rcon_plane_mask_source (r : Fin 10) (p : Fin 8) :
    (if ((rcon (r.val + 1))[0]).toBitVec.getLsbD p.val then (0xf0000000 : BitVec 64) else 0) =
      if r.val < 8 then (if p.val = r.val then 0xf0000000 else 0)
      else (if p.val = r.val - 8 then 0xf0000000 else 0) ^^^
        (if p.val = r.val - 7 then 0xf0000000 else 0) ^^^
        (if p.val = r.val - 5 then 0xf0000000 else 0) ^^^
        (if p.val = r.val - 4 then 0xf0000000 else 0) := by
  decide +kernel +revert

attribute [local irreducible] Standards.NIST.AES.sbox Standards.NIST.AES.pow
  Standards.NIST.AES.keyExpansion roundKeyBlock

set_option maxHeartbeats 800000 in
theorem xorColumns_roundKeyBlock (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hv : v ≠ .aes192) (hstart : v.Nk ≤ 4 * round.val) :
    let boundary := 4 * round.val % v.Nk = 0
    let previous := roundKeyBlock v key ⟨round.val - 1, by have := round.isLt; omega⟩
    let back := roundKeyBlock v key ⟨round.val - v.Nk / 4, by have := round.isLt; omega⟩
    let c := if boundary then (rcon (4 * round.val / v.Nk))[0] else 0
    xorColumns (encodeStandard (fun _ ↦ back))
      (fun p ↦ encodeStandard (fun _ ↦ subBytes previous) p ^^^
        (if c.toBitVec.getLsbD p.val then (0xf0000000 : BitVec 64) else 0))
      (if boundary then 28 else 12) =
        encodeStandard (fun _ ↦ roundKeyBlock v key round) := by
  have hr := round.isLt
  have hNk : v.Nk = 4 ∨ v.Nk = 8 := by
    cases v with
    | aes128 => exact Or.inl rfl
    | aes192 => exact False.elim (hv rfl)
    | aes256 => exact Or.inr rfl
  have hpos : 0 < round.val := by rcases hNk with h | h <;> omega
  have hprev : 4 * (round.val - 1) + 3 = 4 * round.val - 1 := by omega
  have hback (j : Nat) (hj : j < 4) :
      4 * (round.val - v.Nk / 4) + j = 4 * round.val + j - v.Nk := by
    rcases hNk with h | h <;> rw [h] <;> omega
  let w := keyExpansion v key
  let previous := roundKeyBlock v key ⟨round.val - 1, by omega⟩
  let back := roundKeyBlock v key ⟨round.val - v.Nk / 4, by omega⟩
  let c := if 4 * round.val % v.Nk = 0 then (rcon (4 * round.val / v.Nk))[0] else 0
  have hlast (r : Fin 4) : previous[12 + r.val]'(by have := r.isLt; omega) =
      (w[4 * round.val - 1]'(by omega))[r] := by
    have rd : (12 + r.val) / 4 = 3 := by omega
    have rm : (12 + r.val) % 4 = r.val := by omega
    simp only [previous, roundKeyBlock, roundKey, Vector.getElem_ofFn,
      Fin.getElem_fin, rd, rm, hprev, w]
  have hb (r col : Fin 4) : back[4 * col.val + r.val]'(by have := r.isLt; have := col.isLt; omega) =
      (w[4 * round.val + col.val - v.Nk]'(by have := col.isLt; omega))[r] := by
    have rd : (4 * col.val + r.val) / 4 = col.val := by omega
    have rm : (4 * col.val + r.val) % 4 = r.val := by omega
    simp only [back, roundKeyBlock, roundKey, Vector.getElem_ofFn,
      Fin.getElem_fin, rd, rm, hback col.val col.isLt, w]
  have hb00 : back[0] =
      (w[4 * round.val + 0 - v.Nk]'(by omega))[0] := hb 0 0
  have hb10 : back[1] =
      (w[4 * round.val + 0 - v.Nk]'(by omega))[1] := hb 1 0
  have hb20 : back[2] =
      (w[4 * round.val + 0 - v.Nk]'(by omega))[2] := hb 2 0
  have hb30 : back[3] =
      (w[4 * round.val + 0 - v.Nk]'(by omega))[3] := hb 3 0
  have hb01 : back[4] =
      (w[4 * round.val + 1 - v.Nk]'(by omega))[0] := hb 0 1
  have hb11 : back[5] =
      (w[4 * round.val + 1 - v.Nk]'(by omega))[1] := hb 1 1
  have hb21 : back[6] =
      (w[4 * round.val + 1 - v.Nk]'(by omega))[2] := hb 2 1
  have hb31 : back[7] =
      (w[4 * round.val + 1 - v.Nk]'(by omega))[3] := hb 3 1
  have hb02 : back[8] =
      (w[4 * round.val + 2 - v.Nk]'(by omega))[0] := hb 0 2
  have hb12 : back[9] =
      (w[4 * round.val + 2 - v.Nk]'(by omega))[1] := hb 1 2
  have hb22 : back[10] =
      (w[4 * round.val + 2 - v.Nk]'(by omega))[2] := hb 2 2
  have hb32 : back[11] =
      (w[4 * round.val + 2 - v.Nk]'(by omega))[3] := hb 3 2
  have hb03 : back[12] =
      (w[4 * round.val + 3 - v.Nk]'(by omega))[0] := hb 0 3
  have hb13 : back[13] =
      (w[4 * round.val + 3 - v.Nk]'(by omega))[1] := hb 1 3
  have hb23 : back[14] =
      (w[4 * round.val + 3 - v.Nk]'(by omega))[2] := hb 2 3
  have hb33 : back[15] =
      (w[4 * round.val + 3 - v.Nk]'(by omega))[3] := hb 3 3
  have hl0 : previous[12] = (w[4 * round.val - 1]'(by omega))[0] := hlast 0
  have hl1 : previous[13] = (w[4 * round.val - 1]'(by omega))[1] := hlast 1
  have hl2 : previous[14] = (w[4 * round.val - 1]'(by omega))[2] := hlast 2
  have hl3 : previous[15] = (w[4 * round.val - 1]'(by omega))[3] := hlast 3
  have hstep := keyExpansion_four_word_recurrence v key round hv hstart
  change xorColumns (encode (fromStandard (fun _ ↦ back)))
    (fun p ↦ encode (fromStandard (fun _ ↦ subBytes previous)) p ^^^
      (if c.toBitVec.getLsbD p.val then (0xf0000000 : BitVec 64) else 0))
    (if 4 * round.val % v.Nk = 0 then 28 else 12) =
      encode (fromStandard (fun _ ↦ roundKeyBlock v key round))
  rw [encode_rcon_byte]
  by_cases hboundary : 4 * round.val % v.Nk = 0
  · have ht : expansionTemp v (4 * round.val) (w[4 * round.val - 1]'(by omega)) =
        xorWord (subWord (rotWord (w[4 * round.val - 1]'(by omega))))
          (rcon (4 * round.val / v.Nk)) := by
      simp only [expansionTemp, ite_eq_left hboundary]
    simp only [hboundary, ↓reduceIte]
    rw [show 28 = 16 * (1 : Fin 2).val + 12 from rfl, xorColumns_encode]
    apply congrArg encode
    funext b j
    change _ = (roundKeyBlock v key round)[j.val].toBitVec
    conv => rhs; unfold roundKeyBlock; rw [hstep]
    have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨
      j.val = 7 ∨ j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11 ∨ j.val = 12 ∨ j.val = 13 ∨
      j.val = 14 ∨ j.val = 15 := by omega
    rcases hj with hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj
    all_goals simp only [hj, xorColumnsBlocks, fromStandard,
      Standards.NIST.AES.subBytes, Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Fin.isValue, Fin.val_one, Nat.reduceEqDiff,
      ↓reduceIte,
      hb00, hb10, hb20, hb30, hb01, hb11, hb21, hb31, hb02, hb12, hb22, hb32, hb03, hb13, hb23,
      hb33, hl0, hl1, hl2, hl3, w, c, hboundary, ↓reduceIte,
      ht, xorWord, subWord, rotWord, rcon,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      UInt8.toBitVec_xor]
    all_goals ac_rfl
  · have hn : v.Nk > 6 ∧ (4 * round.val) % v.Nk = 4 := by
      rcases hNk with h | h
      · rw [h] at hboundary
        omega
      · rw [h] at hboundary ⊢
        omega
    have ht : expansionTemp v (4 * round.val) (w[4 * round.val - 1]'(by omega)) =
        subWord (w[4 * round.val - 1]'(by omega)) := by
      simp only [expansionTemp, ite_eq_right hboundary, ite_eq_left hn]
    simp only [hboundary, ↓reduceIte]
    rw [show 12 = 16 * (0 : Fin 2).val + 12 from rfl, xorColumns_encode]
    apply congrArg encode
    funext b j
    change _ = (roundKeyBlock v key round)[j.val].toBitVec
    conv => rhs; unfold roundKeyBlock; rw [hstep]
    have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨
      j.val = 7 ∨ j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11 ∨ j.val = 12 ∨ j.val = 13 ∨
      j.val = 14 ∨ j.val = 15 := by omega
    rcases hj with hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj
    all_goals simp only [hj, xorColumnsBlocks, fromStandard,
      Standards.NIST.AES.subBytes, Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Fin.isValue, Fin.val_zero, Nat.reduceEqDiff,
      ↓reduceIte,
      hb00, hb10, hb20, hb30, hb01, hb11, hb21, hb31, hb02, hb12, hb22, hb32, hb03, hb13, hb23,
      hb33, hl0, hl1, hl2, hl3, w, c, hboundary, ↓reduceIte,
      ht, xorWord, subWord,       Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ,
      UInt8.toBitVec_xor]
    all_goals ac_rfl

end AesGcm.Proofs.Machine.KeySchedule
