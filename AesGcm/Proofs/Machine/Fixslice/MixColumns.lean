import AesGcm.Proofs.Machine.Fixslice.Operations
import AesGcm.Proofs.Machine.Fixslice.Linear

namespace AesGcm.Proofs.Machine.Fixslice

open Standards.NIST.AES

def xtimePlanes (a : Planes) : Planes := fun p ↦
  match p.val with
  | 0 => a 7
  | 1 => a 0 ^^^ a 7
  | 2 => a 1
  | 3 => a 2 ^^^ a 7
  | 4 => a 3 ^^^ a 7
  | 5 => a 4
  | 6 => a 5
  | _ => a 6

def xtimeBlocks (x : Blocks) : Blocks := fun b j ↦ (xtimes (UInt8.ofBitVec (x b j))).toBitVec

def mapPlanes (f : BitVec 64 → BitVec 64) (a : Planes) : Planes := fun p ↦ f (a p)

def mixColumnsCircuit (first second : BitVec 64 → BitVec 64) (a : Planes) : Planes :=
  let b := mapPlanes first a
  let c := xorPlanes a b
  xorPlanes (xorPlanes b (xtimePlanes c)) (mapPlanes second c)

def invMixColumnsCircuit (first second : BitVec 64 → BitVec 64) (a : Planes) : Planes :=
  let b := mapPlanes first a
  let c := xorPlanes a b
  let d := xorPlanes a (xtimePlanes c)
  let e := xorPlanes c (xtimePlanes (xtimePlanes d))
  xorPlanes (xorPlanes d e) (mapPlanes second e)

private def xtimeBits (a : Fin 8 → Bool) (p : Fin 8) : Bool :=
  match p.val with
  | 0 => a 7
  | 1 => a 0 ^^ a 7
  | 2 => a 1
  | 3 => a 2 ^^ a 7
  | 4 => a 3 ^^ a 7
  | 5 => a 4
  | 6 => a 5
  | _ => a 6

private theorem getLsbD_xtimes (x : UInt8) (p : Fin 8) :
    (xtimes x).toBitVec.getLsbD p.val = xtimeBits (fun q ↦ x.toBitVec.getLsbD q.val) p := by
  have h : ∀ x : Fin 256, ∀ p : Fin 8,
      (xtimes (UInt8.ofFin x)).toBitVec.getLsbD p.val =
        xtimeBits (fun q ↦ (UInt8.ofFin x).toBitVec.getLsbD q.val) p := by decide +kernel
  exact h x.toFin p

private theorem getLsbD_xtimePlanes (a : Planes) (p : Fin 8) (i : Nat) :
    (xtimePlanes a p).getLsbD i = xtimeBits (fun q ↦ (a q).getLsbD i) p := by
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
    have := p.isLt
    omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact BitVec.getLsbD_xor

theorem xtimePlanes_encode (x : Blocks) : xtimePlanes (encode x) = encode (xtimeBlocks x) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let b : Fin 4 := ⟨i % 4, by omega⟩
  let j : Fin 16 := ⟨4 * (i / 4 % 4) + i / 16, by omega⟩
  calc
    _ = xtimeBits (fun q ↦ (encode x q).getLsbD i) p := getLsbD_xtimePlanes _ _ _
    _ = xtimeBits (fun q ↦ (x b j).getLsbD q.val) p := by
      apply congrArg (fun f ↦ xtimeBits f p)
      funext q
      exact getLsbD_encode x q ⟨i, hi⟩
    _ = (xtimes (UInt8.ofBitVec (x b j))).toBitVec.getLsbD p.val :=
      (getLsbD_xtimes (UInt8.ofBitVec (x b j)) p).symm
    _ = _ := (getLsbD_encode (xtimeBlocks x) p ⟨i, hi⟩).symm


def mixColumnsBlocks (first second : Blocks → Blocks) (x : Blocks) : Blocks :=
  let b := first x
  let c := xorBlocks x b
  xorBlocks (xorBlocks b (xtimeBlocks c)) (second c)

def invMixColumnsBlocks (first second : Blocks → Blocks) (x : Blocks) : Blocks :=
  let b := first x
  let c := xorBlocks x b
  let d := xorBlocks x (xtimeBlocks c)
  let e := xorBlocks c (xtimeBlocks (xtimeBlocks d))
  xorBlocks (xorBlocks d e) (second e)

theorem mixColumnsCircuit_encode (first second : BitVec 64 → BitVec 64)
    (f g : Blocks → Blocks)
    (hf : ∀ x, mapPlanes first (encode x) = encode (f x))
    (hg : ∀ x, mapPlanes second (encode x) = encode (g x)) (x : Blocks) :
    mixColumnsCircuit first second (encode x) = encode (mixColumnsBlocks f g x) := by
  simp only [mixColumnsCircuit, mixColumnsBlocks, hf, ← encode_xorBlocks,
    xtimePlanes_encode, hg]

theorem invMixColumnsCircuit_encode (first second : BitVec 64 → BitVec 64)
    (f g : Blocks → Blocks)
    (hf : ∀ x, mapPlanes first (encode x) = encode (f x))
    (hg : ∀ x, mapPlanes second (encode x) = encode (g x)) (x : Blocks) :
    invMixColumnsCircuit first second (encode x) = encode (invMixColumnsBlocks f g x) := by
  simp only [invMixColumnsCircuit, invMixColumnsBlocks, hf, ← encode_xorBlocks,
    xtimePlanes_encode, hg]


def rotateByteIndex (r c : Nat) (j : Fin 16) : Fin 16 :=
  ⟨(j.val % 4 + r) % 4 + 4 * ((j.val / 4 + c) % 4), by omega⟩

def rotateBlocks (r c : Nat) (x : Blocks) : Blocks := fun b j ↦
  x b (rotateByteIndex r c j)

theorem rotateByteIndex_add (r c s d : Nat) (j : Fin 16) :
    rotateByteIndex r c (rotateByteIndex s d j) = rotateByteIndex (r + s) (c + d) j := by
  apply Fin.ext
  simp only [rotateByteIndex, Fin.val_mk]
  omega

theorem mapPlanes_rotate_encode (f : BitVec 64 → BitVec 64) (r c : Nat)
    (h : ∀ (x : BitVec 64) (i : Fin 64),
      (f x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex r c i.val))
    (x : Blocks) : mapPlanes f (encode x) = encode (rotateBlocks r c x) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : rotateRowsColumnsIndex r c i < 64 := by
    simp only [rotateRowsColumnsIndex]
    omega
  change (f (encode x p)).getLsbD i = _
  rw [h _ ⟨i, hi⟩, getLsbD_encode _ _ ⟨_, hb⟩, getLsbD_encode _ _ ⟨i, hi⟩]
  have hs : rotateRowsColumnsIndex r c i % 4 = i % 4 ∧
      rotateRowsColumnsIndex r c i / 16 = (i / 16 + r) % 4 ∧
      rotateRowsColumnsIndex r c i / 4 % 4 = (i / 4 % 4 + c) % 4 := by
    unfold rotateRowsColumnsIndex
    omega
  have ht : (4 * (i / 4 % 4) + i / 16) / 4 = i / 4 % 4 ∧
      (4 * (i / 4 % 4) + i / 16) % 4 = i / 16 := by omega
  simp only [rotateBlocks, rotateByteIndex, hs.1, hs.2.1, hs.2.2, ht.1, ht.2]
  congr 2
  apply Fin.ext
  dsimp only
  omega

def mixColumns0 := mixColumnsCircuit rotateRows1 rotateRows2
def mixColumns1 := mixColumnsCircuit rotateRowsAndColumns11 rotateRowsAndColumns22
def mixColumns2 := mixColumnsCircuit rotateRowsAndColumns12 rotateRows2
def mixColumns3 := mixColumnsCircuit rotateRowsAndColumns13 rotateRowsAndColumns22

def invMixColumns0 := invMixColumnsCircuit rotateRows1 rotateRows2
def invMixColumns1 := invMixColumnsCircuit rotateRowsAndColumns11 rotateRowsAndColumns22
def invMixColumns2 := invMixColumnsCircuit rotateRowsAndColumns12 rotateRows2
def invMixColumns3 := invMixColumnsCircuit rotateRowsAndColumns13 rotateRowsAndColumns22

theorem mixColumns0_encode (x : Blocks) :
    mixColumns0 (encode x) =
      encode (mixColumnsBlocks (rotateBlocks 1 0) (rotateBlocks 2 0) x) :=
  mixColumnsCircuit_encode rotateRows1 rotateRows2 _ _
    (mapPlanes_rotate_encode rotateRows1 1 0 getLsbD_rotateRows1)
    (mapPlanes_rotate_encode rotateRows2 2 0 getLsbD_rotateRows2) x

theorem mixColumns1_encode (x : Blocks) :
    mixColumns1 (encode x) =
      encode (mixColumnsBlocks (rotateBlocks 1 1) (rotateBlocks 2 2) x) :=
  mixColumnsCircuit_encode rotateRowsAndColumns11 rotateRowsAndColumns22 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns11 1 1 getLsbD_rotateRowsAndColumns11)
    (mapPlanes_rotate_encode rotateRowsAndColumns22 2 2 getLsbD_rotateRowsAndColumns22) x

theorem mixColumns2_encode (x : Blocks) :
    mixColumns2 (encode x) =
      encode (mixColumnsBlocks (rotateBlocks 1 2) (rotateBlocks 2 0) x) :=
  mixColumnsCircuit_encode rotateRowsAndColumns12 rotateRows2 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns12 1 2 getLsbD_rotateRowsAndColumns12)
    (mapPlanes_rotate_encode rotateRows2 2 0 getLsbD_rotateRows2) x

theorem mixColumns3_encode (x : Blocks) :
    mixColumns3 (encode x) =
      encode (mixColumnsBlocks (rotateBlocks 1 3) (rotateBlocks 2 2) x) :=
  mixColumnsCircuit_encode rotateRowsAndColumns13 rotateRowsAndColumns22 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns13 1 3 getLsbD_rotateRowsAndColumns13)
    (mapPlanes_rotate_encode rotateRowsAndColumns22 2 2 getLsbD_rotateRowsAndColumns22) x

theorem invMixColumns0_encode (x : Blocks) :
    invMixColumns0 (encode x) =
      encode (invMixColumnsBlocks (rotateBlocks 1 0) (rotateBlocks 2 0) x) :=
  invMixColumnsCircuit_encode rotateRows1 rotateRows2 _ _
    (mapPlanes_rotate_encode rotateRows1 1 0 getLsbD_rotateRows1)
    (mapPlanes_rotate_encode rotateRows2 2 0 getLsbD_rotateRows2) x

theorem invMixColumns1_encode (x : Blocks) :
    invMixColumns1 (encode x) =
      encode (invMixColumnsBlocks (rotateBlocks 1 1) (rotateBlocks 2 2) x) :=
  invMixColumnsCircuit_encode rotateRowsAndColumns11 rotateRowsAndColumns22 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns11 1 1 getLsbD_rotateRowsAndColumns11)
    (mapPlanes_rotate_encode rotateRowsAndColumns22 2 2 getLsbD_rotateRowsAndColumns22) x

theorem invMixColumns2_encode (x : Blocks) :
    invMixColumns2 (encode x) =
      encode (invMixColumnsBlocks (rotateBlocks 1 2) (rotateBlocks 2 0) x) :=
  invMixColumnsCircuit_encode rotateRowsAndColumns12 rotateRows2 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns12 1 2 getLsbD_rotateRowsAndColumns12)
    (mapPlanes_rotate_encode rotateRows2 2 0 getLsbD_rotateRows2) x

theorem invMixColumns3_encode (x : Blocks) :
    invMixColumns3 (encode x) =
      encode (invMixColumnsBlocks (rotateBlocks 1 3) (rotateBlocks 2 2) x) :=
  invMixColumnsCircuit_encode rotateRowsAndColumns13 rotateRowsAndColumns22 _ _
    (mapPlanes_rotate_encode rotateRowsAndColumns13 1 3 getLsbD_rotateRowsAndColumns13)
    (mapPlanes_rotate_encode rotateRowsAndColumns22 2 2 getLsbD_rotateRowsAndColumns22) x

private theorem mul_one (x : UInt8) : mul 1 x = x := by
  have h : ∀ x : Fin 256, mul 1 (UInt8.ofFin x) = UInt8.ofFin x := by decide +kernel
  exact h x.toFin

private theorem mul_two (x : UInt8) : mul 2 x = xtimes x := by
  have h : ∀ x : Fin 256, mul 2 (UInt8.ofFin x) = xtimes (UInt8.ofFin x) := by decide +kernel
  exact h x.toFin

private theorem mul_three (x : UInt8) : mul 3 x = xtimes x ^^^ x := by
  have h : ∀ x : Fin 256, mul 3 (UInt8.ofFin x) = xtimes (UInt8.ofFin x) ^^^ UInt8.ofFin x := by
    decide +kernel
  exact h x.toFin

private theorem mul_fourteen (x : UInt8) :
    mul 14 x = xtimes (xtimes (xtimes x)) ^^^ xtimes (xtimes x) ^^^ xtimes x := by
  have h : ∀ x : Fin 256, mul 14 (UInt8.ofFin x) =
      xtimes (xtimes (xtimes (UInt8.ofFin x))) ^^^ xtimes (xtimes (UInt8.ofFin x)) ^^^
        xtimes (UInt8.ofFin x) := by decide +kernel
  exact h x.toFin

private theorem mul_eleven (x : UInt8) :
    mul 11 x = xtimes (xtimes (xtimes x)) ^^^ xtimes x ^^^ x := by
  have h : ∀ x : Fin 256, mul 11 (UInt8.ofFin x) =
      xtimes (xtimes (xtimes (UInt8.ofFin x))) ^^^ xtimes (UInt8.ofFin x) ^^^
        UInt8.ofFin x := by decide +kernel
  exact h x.toFin

private theorem mul_thirteen (x : UInt8) :
    mul 13 x = xtimes (xtimes (xtimes x)) ^^^ xtimes (xtimes x) ^^^ x := by
  have h : ∀ x : Fin 256, mul 13 (UInt8.ofFin x) =
      xtimes (xtimes (xtimes (UInt8.ofFin x))) ^^^ xtimes (xtimes (UInt8.ofFin x)) ^^^
        UInt8.ofFin x := by decide +kernel
  exact h x.toFin

private theorem mul_nine (x : UInt8) : mul 9 x = xtimes (xtimes (xtimes x)) ^^^ x := by
  have h : ∀ x : Fin 256, mul 9 (UInt8.ofFin x) =
      xtimes (xtimes (xtimes (UInt8.ofFin x))) ^^^ UInt8.ofFin x := by decide +kernel
  exact h x.toFin

private theorem xtimes_xor (x y : UInt8) : xtimes (x ^^^ y) = xtimes x ^^^ xtimes y := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  rw [getLsbD_xtimes _ ⟨i, hi⟩, getLsbD_xtimes _ ⟨i, hi⟩, getLsbD_xtimes _ ⟨i, hi⟩]
  have hp : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [xtimeBits, UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  all_goals simp only [Bool.xor_assoc, Bool.xor_left_comm]

private theorem mixColumn_byte (a b c d : UInt8) :
    b ^^^ xtimes (a ^^^ b) ^^^ (c ^^^ d) =
      mul 2 a ^^^ mul 3 b ^^^ mul 1 c ^^^ mul 1 d := by
  simp only [xtimes_xor, mul_two, mul_three, mul_one]
  ac_rfl

private theorem byte_xor_left_comm (a b c : UInt8) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by ac_rfl

private theorem byte_xor_cancel_left (a b : UInt8) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

private theorem invMixColumn_byte (a b c d : UInt8) :
    let da := a ^^^ xtimes (a ^^^ b)
    let dc := c ^^^ xtimes (c ^^^ d)
    let ea := (a ^^^ b) ^^^ xtimes (xtimes da)
    let ec := (c ^^^ d) ^^^ xtimes (xtimes dc)
    da ^^^ ea ^^^ ec = mul 14 a ^^^ mul 11 b ^^^ mul 13 c ^^^ mul 9 d := by
  simp only [xtimes_xor, mul_fourteen, mul_eleven, mul_thirteen, mul_nine]
  simp only [UInt8.xor_assoc, UInt8.xor_comm, byte_xor_left_comm, byte_xor_cancel_left,
    ]


theorem mixColumnsBlocks_rotate_get (k : Nat) (x : Blocks) (b : Fin 4) (j : Fin 16) :
    UInt8.ofBitVec (mixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k)) x b j) =
      mul 2 (UInt8.ofBitVec (x b j)) ^^^
      mul 3 (UInt8.ofBitVec (x b (rotateByteIndex 1 k j))) ^^^
      mul 1 (UInt8.ofBitVec (x b (rotateByteIndex 2 (2 * k) j))) ^^^
      mul 1 (UInt8.ofBitVec (x b (rotateByteIndex 3 (3 * k) j))) := by
  simp only [mixColumnsBlocks, xorBlocks, xtimeBlocks, rotateBlocks, UInt8.ofBitVec_xor,
    UInt8.ofBitVec_toBitVec, rotateByteIndex_add]
  rw [show 1 + 2 = 3 from rfl, show k + 2 * k = 3 * k by omega]
  exact mixColumn_byte _ _ _ _

theorem invMixColumnsBlocks_rotate_get (k : Nat) (x : Blocks) (b : Fin 4) (j : Fin 16) :
    UInt8.ofBitVec (invMixColumnsBlocks (rotateBlocks 1 k) (rotateBlocks 2 (2 * k)) x b j) =
      mul 14 (UInt8.ofBitVec (x b j)) ^^^
      mul 11 (UInt8.ofBitVec (x b (rotateByteIndex 1 k j))) ^^^
      mul 13 (UInt8.ofBitVec (x b (rotateByteIndex 2 (2 * k) j))) ^^^
      mul 9 (UInt8.ofBitVec (x b (rotateByteIndex 3 (3 * k) j))) := by
  simp only [invMixColumnsBlocks, xorBlocks, xtimeBlocks, rotateBlocks, UInt8.ofBitVec_xor,
    UInt8.ofBitVec_toBitVec, rotateByteIndex_add]
  rw [show 1 + 2 = 3 from rfl, show k + 2 * k = 3 * k by omega]
  exact invMixColumn_byte _ _ _ _

end AesGcm.Proofs.Machine.Fixslice
