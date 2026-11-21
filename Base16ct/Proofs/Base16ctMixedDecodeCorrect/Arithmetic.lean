import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Nibble

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

def high32 (c : UInt8) : BitVec 32 :=
  let x := c.toBitVec.zeroExtend 32
  let digitMask := (((47 - x) &&& (x - 58)).setWidth 16).signExtend 32 >>> 8
  let upperMask := (((64 - x) &&& (x - 71)).setWidth 16).signExtend 32 >>> 8
  let lowerMask := (((96 - x) &&& (x - 103)).setWidth 16).signExtend 32 >>> 8
  ((((x + 4049) &&& digitMask) + ((x + 4042) &&& upperMask) +
    ((x + 4010) &&& lowerMask)) <<< 4) - 16

def low32 (c : UInt8) : BitVec 32 :=
  let x := c.toBitVec.zeroExtend 32
  let digitMask := ((((47 - x) &&& (x - 58)).setWidth 16).signExtend 32).sshiftRight 8
  let upperMask := ((((64 - x) &&& (x - 71)).setWidth 16).signExtend 32).sshiftRight 8
  let lowerMask := ((((96 - x) &&& (x - 103)).setWidth 16).signExtend 32).sshiftRight 8
  ((x - 47) &&& digitMask) + ((x - 54) &&& upperMask) + ((x - 86) &&& lowerMask) - 1

def pairWord (hi lo : UInt8) : BitVec 32 := low32 lo ||| high32 hi

theorem high32_eq (c : UInt8) :
    high32 c = match mixedNibble c with
      | some n => BitVec.ofNat 32 (65536 + 16 * n)
      | none => -16 := by
  have h : ∀ b : BitVec 8, high32 (⟨b⟩ : UInt8) = match mixedNibble (⟨b⟩ : UInt8) with
      | some n => BitVec.ofNat 32 (65536 + 16 * n)
      | none => -16 := by decide +kernel
  exact h c.toBitVec

theorem low32_eq (c : UInt8) :
    low32 c = match mixedNibble c with
      | some n => BitVec.ofNat 32 n
      | none => -1 := by
  have h : ∀ b : BitVec 8, low32 (⟨b⟩ : UInt8) = match mixedNibble (⟨b⟩ : UInt8) with
      | some n => BitVec.ofNat 32 n
      | none => -1 := by decide +kernel
  exact h c.toBitVec


theorem pairWord_byte {hi lo : UInt8} {h l : Nat}
    (hh : mixedNibble hi = some h) (hl : mixedNibble lo = some l) :
    (pairWord hi lo).setWidth 8 = (UInt8.ofNat (16 * h + l)).toBitVec := by
  have ht := mixedNibble_lt hh
  have lt := mixedNibble_lt hl
  have calc_eq : ∀ a b : Fin 16,
      ((BitVec.ofNat 32 b.val) ||| (BitVec.ofNat 32 (65536 + 16 * a.val))).setWidth 8 =
        (UInt8.ofNat (16 * a.val + b.val)).toBitVec := by decide +kernel
  simpa only [pairWord, high32_eq, low32_eq, hh, hl] using
    calc_eq ⟨h, ht⟩ ⟨l, lt⟩

theorem pairWord_marker (hi lo : UInt8) :
    (pairWord hi lo).extractLsb' 8 8 =
      if (mixedNibble hi).isSome && (mixedNibble lo).isSome then 0 else 255 := by
  unfold pairWord
  rw [high32_eq, low32_eq]
  cases hh : mixedNibble hi with
  | none =>
      cases hl : mixedNibble lo with
      | none => decide +kernel
      | some l =>
          have calc_eq : ∀ b : Fin 16,
              ((BitVec.ofNat 32 b.val) ||| (-16 : BitVec 32)).extractLsb' 8 8 = 255 := by
            decide +kernel
          exact calc_eq ⟨l, mixedNibble_lt hl⟩
  | some h =>
      cases hl : mixedNibble lo with
      | none =>
          change ((BitVec.allOnes 32) ||| _).extractLsb' 8 8 = 255
          rw [BitVec.allOnes_or]
          decide +kernel
      | some l =>
          have calc_eq : ∀ a b : Fin 16,
              ((BitVec.ofNat 32 b.val) |||
                (BitVec.ofNat 32 (65536 + 16 * a.val))).extractLsb' 8 8 = 0 := by
            decide +kernel
          exact calc_eq ⟨h, mixedNibble_lt hh⟩ ⟨l, mixedNibble_lt hl⟩


theorem pairWord_accumulate_eq (acc : BitVec 64) (hi lo : UInt8)
    (ha : acc = 0 ∨ acc = 255) :
    ((acc.setWidth 32 |||
      (((pairWord hi lo).setWidth 64).extractLsb' 8 8).setWidth 32).setWidth 64) =
      acc ||| ((pairWord hi lo).extractLsb' 8 8).setWidth 64 := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide), pairWord_marker]
  rcases ha with rfl | rfl <;> split <;> decide +kernel

theorem pairWord_accumulate_cases (acc : BitVec 64) (hi lo : UInt8)
    (ha : acc = 0 ∨ acc = 255) :
    (acc ||| ((pairWord hi lo).extractLsb' 8 8).setWidth 64) = 0 ∨
      (acc ||| ((pairWord hi lo).extractLsb' 8 8).setWidth 64) = 255 := by
  rw [pairWord_marker]
  rcases ha with rfl | rfl <;> split <;> decide +kernel

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
