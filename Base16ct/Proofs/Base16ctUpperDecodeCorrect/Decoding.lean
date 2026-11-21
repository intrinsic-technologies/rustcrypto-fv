import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Compatibility

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

open Base16ct.Spec Base16ct.Spec.Program

def decodeLetterOffset : RFC4648.Alphabet → BitVec 32
  | .lower => 0x60
  | .upper => 0x40

def decodeRangeMask (lo hi c : BitVec 32) : BitVec 32 :=
  ((lo - c) &&& (c - hi)).setWidth 16 |>.signExtend 32

def decodeLowNibble (alphabets : List RFC4648.Alphabet) (byte : UInt8) : BitVec 32 :=
  let c := byte.toBitVec.setWidth 32
  let digit := (decodeRangeMask 0x2f 0x3a c).sshiftRight 8 &&& (c - 0x2f)
  let sum := alphabets.foldl (fun acc alphabet =>
    let offset := decodeLetterOffset alphabet
    acc + ((decodeRangeMask offset (offset + 7) c).sshiftRight 8 &&& (c - (offset - 10)))) digit
  sum - 1

def decodeHighNibble (alphabets : List RFC4648.Alphabet) (byte : UInt8) : BitVec 32 :=
  let c := byte.toBitVec.setWidth 32
  let digit := (decodeRangeMask 0x2f 0x3a c >>> 8) &&& (c + 0xfd1)
  let sum := alphabets.foldl (fun acc alphabet =>
    let offset := decodeLetterOffset alphabet
    acc + ((decodeRangeMask offset (offset + 7) c >>> 8) &&& (c + (0x100a - offset)))) digit
  (sum <<< 4) - 16

theorem decodeLowNibble_correct (alphabets : List RFC4648.Alphabet) (byte : UInt8)
    (ha : alphabets ∈ [[.lower], [.upper], RFC4648.caseInsensitive]) :
    decodeLowNibble alphabets byte =
      match RFC4648.valueOfCharacter alphabets byte with
      | some n => BitVec.ofNat 32 n
      | none => -1 := by
  have h : ∀ n : Fin 256, decodeLowNibble alphabets (UInt8.ofNat n.val) =
      match RFC4648.valueOfCharacter alphabets (UInt8.ofNat n.val) with
      | some v => BitVec.ofNat 32 v
      | none => -1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide +kernel
  simpa using h ⟨byte.toNat, byte.toFin.isLt⟩

theorem decodeHighNibble_correct (alphabets : List RFC4648.Alphabet) (byte : UInt8)
    (ha : alphabets ∈ [[.lower], [.upper], RFC4648.caseInsensitive]) :
    decodeHighNibble alphabets byte =
      match RFC4648.valueOfCharacter alphabets byte with
      | some n => 0x10000 + BitVec.ofNat 32 (16 * n)
      | none => -16 := by
  have h : ∀ n : Fin 256, decodeHighNibble alphabets (UInt8.ofNat n.val) =
      match RFC4648.valueOfCharacter alphabets (UInt8.ofNat n.val) with
      | some v => 0x10000 + BitVec.ofNat 32 (16 * v)
      | none => -16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide +kernel
  simpa using h ⟨byte.toNat, byte.toFin.isLt⟩

theorem valueOfCharacter_lt {alphabets : List RFC4648.Alphabet} {byte : UInt8} {n : Nat}
    (h : RFC4648.valueOfCharacter alphabets byte = some n) : n < 16 := by
  obtain ⟨alphabet, _, hidx⟩ := List.exists_of_findSome?_eq_some h
  have hv := (List.idxOf?_eq_some_iff.mp hidx).choose
  cases alphabet <;> simpa [RFC4648.Alphabet.table] using hv

def decodePair (alphabets : List RFC4648.Alphabet) (high low : UInt8) : BitVec 32 :=
  decodeHighNibble alphabets high ||| decodeLowNibble alphabets low

theorem decodePair_correct (alphabets : List RFC4648.Alphabet) (high low : UInt8)
    (ha : alphabets ∈ [[.lower], [.upper], RFC4648.caseInsensitive]) :
    (do
      let h ← RFC4648.valueOfCharacter alphabets high
      let l ← RFC4648.valueOfCharacter alphabets low
      pure (UInt8.ofNat (16 * h + l))) =
      if (decodePair alphabets high low).extractLsb' 8 8 = 0 then
        some (UInt8.ofBitVec ((decodePair alphabets high low).setWidth 8))
      else none := by
  have finite : ∀ h l : Fin 16,
      ((0x10000 + BitVec.ofNat 32 (16 * h.val)) ||| BitVec.ofNat 32 l.val).extractLsb' 8 8 = 0 ∧
      (((0x10000 + BitVec.ofNat 32 (16 * h.val)) |||
        BitVec.ofNat 32 l.val).setWidth 8) = BitVec.ofNat 8 (16 * h.val + l.val) := by
    decide +kernel
  simp only [decodePair, decodeHighNibble_correct alphabets high ha,
    decodeLowNibble_correct alphabets low ha]
  cases hh : RFC4648.valueOfCharacter alphabets high with
  | none => simp [BitVec.extractLsb'_or]
  | some h =>
    cases hl : RFC4648.valueOfCharacter alphabets low with
    | none => simp
    | some l =>
      have hv := finite ⟨h, valueOfCharacter_lt hh⟩ ⟨l, valueOfCharacter_lt hl⟩
      rw [hv.1, ite_eq_left rfl, hv.2]
      rfl

def decodeLoop (alphabets : List RFC4648.Alphabet) : List UInt8 → List UInt8 × BitVec 8
  | [] => ([], 0)
  | [_] => ([], 255)
  | high :: low :: rest =>
    let pair := decodePair alphabets high low
    let tail := decodeLoop alphabets rest
    (UInt8.ofBitVec (pair.setWidth 8) :: tail.1, pair.extractLsb' 8 8 ||| tail.2)

theorem decodeLoop_correct (alphabets : List RFC4648.Alphabet) (input : List UInt8)
    (ha : alphabets ∈ [[.lower], [.upper], RFC4648.caseInsensitive]) :
    RFC4648.decode alphabets input =
      if (decodeLoop alphabets input).2 = 0 then some (decodeLoop alphabets input).1 else none := by
  induction input using RFC4648.decode.induct with
  | case1 => rfl
  | case2 high low rest ih =>
    have hp := decodePair_correct alphabets high low ha
    simp only [RFC4648.decode, decodeLoop]
    rw [ih]
    cases hh : RFC4648.valueOfCharacter alphabets high <;>
      cases hl : RFC4648.valueOfCharacter alphabets low <;>
      simp only [hh, hl] at hp ⊢
    all_goals dsimp only [Bind.bind, Option.bind, Pure.pure] at hp ⊢
    all_goals
      split at hp <;> by_cases ht : (decodeLoop alphabets rest).2 = 0 <;>
        simp_all [BitVec.or_eq_zero_iff]
  | case3 byte => rfl

theorem decodeLoop_length (alphabets : List RFC4648.Alphabet) (input : List UInt8) :
    (decodeLoop alphabets input).1.length = input.length / 2 := by
  induction input using RFC4648.decode.induct with
  | case1 => rfl
  | case2 high low rest ih =>
    simp only [decodeLoop, List.length_cons]
    omega
  | case3 byte => simp [decodeLoop]

theorem decodeResult_loop (alphabets : List RFC4648.Alphabet) (input : List UInt8)
    (capacity : Nat) (ha : alphabets ∈ [[.lower], [.upper], RFC4648.caseInsensitive]) :
    pairDecodeResult alphabets input capacity =
      if input.length % 2 ≠ 0 ∨ capacity < input.length / 2 then .error .invalidLength
      else if (decodeLoop alphabets input).2 = 0 then .ok (decodeLoop alphabets input).1
      else .error .invalidEncoding := by
  simp only [pairDecodeResult, decodeLoop_correct alphabets input ha]
  split
  · rfl
  · by_cases hz : (decodeLoop alphabets input).2 = 0 <;>
      simp only [hz, ite_true, ite_false]

theorem decodeLoop_append_even (alphabets : List RFC4648.Alphabet) (pre rest : List UInt8)
    (hpre : pre.length % 2 = 0) :
    decodeLoop alphabets (pre ++ rest) =
      ((decodeLoop alphabets pre).1 ++ (decodeLoop alphabets rest).1,
        (decodeLoop alphabets pre).2 ||| (decodeLoop alphabets rest).2) := by
  induction pre using RFC4648.decode.induct with
  | case1 => simp [decodeLoop]
  | case2 high low pre ih =>
    have hpre' : pre.length % 2 = 0 := by
      simp only [List.length_cons] at hpre
      omega
    rw [List.cons_append, List.cons_append, decodeLoop, decodeLoop, ih hpre']
    simp [BitVec.or_assoc]
  | case3 byte => simp_all

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
