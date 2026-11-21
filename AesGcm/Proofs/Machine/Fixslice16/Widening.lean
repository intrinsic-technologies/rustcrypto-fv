import AesGcm.Proofs.Machine.Fixslice16.Operations
import AesGcm.Proofs.Machine.Fixslice16.Sbox
import AesGcm.Proofs.Machine.Fixslice.Operations

namespace AesGcm.Proofs.Machine.Fixslice16

open AesGcm.Proofs.Machine.Fixslice (fromBits getLsbD_fromBits)

def widenWord (x : BitVec 16) : BitVec 64 :=
  fromBits fun i ↦ x.getLsbD (i.val / 4)

theorem getLsbD_widenWord (x : BitVec 16) (i : Fin 64) :
    (widenWord x).getLsbD i.val = x.getLsbD (i.val / 4) :=
  getLsbD_fromBits _ _

def widenCircuit (x : BitVec 16) : BitVec 64 :=
  let a := x.setWidth 64
  let b := (a * 0x1000001000#64 ||| (a <<< 24 ||| a)) &&& 0x000f000f000f000f#64
  let c := ((b <<< 9) + (b <<< 3)) ||| (b <<< 6 ||| b)
  let d := c &&& 0x1111111111111111#64
  let e := d + d * 4#64
  e + e * 2#64

private theorem masked_shift_add_eq_or {w : Nat} (x y m n : BitVec w) (a b : Nat)
    (h : (m <<< a) &&& (n <<< b) = 0) :
    ((x &&& m) <<< a) + ((y &&& n) <<< b) =
      ((x &&& m) <<< a) ||| ((y &&& n) <<< b) := by
  apply BitVec.add_eq_or_of_and_eq_zero
  rw [BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_and_distrib]
  calc
    _ = ((x <<< a) &&& (y <<< b)) &&& ((m <<< a) &&& (n <<< b)) := by ac_rfl
    _ = 0 := by
      rw [h]
      exact BitVec.and_zero

private theorem masked_shift_add_self {w : Nat} (x m : BitVec w) (a : Nat)
    (h : m &&& (m <<< a) = 0) :
    (x &&& m) + ((x &&& m) <<< a) = (x &&& m) ||| ((x &&& m) <<< a) := by
  simpa only [BitVec.shiftLeft_zero] using masked_shift_add_eq_or x x m m 0 a (by simpa only [BitVec.shiftLeft_zero] using h)

private theorem setWidth16_mask (x : BitVec 16) : x.setWidth 64 &&& 0xffff#64 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h : i < 16
  · have hm : (0xffff#64).getLsbD i = true := by
      change ((BitVec.allOnes 16).setWidth 64).getLsbD i = true
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hi, h,
        decide_true, Bool.and_self]
    simp [hm]
  · simp [BitVec.getLsbD_of_ge x i (by omega)]

def widenBitwise (x : BitVec 16) : BitVec 64 :=
  let a := x.setWidth 64
  let b := (a <<< 12 ||| a <<< 36 ||| (a <<< 24 ||| a)) &&& 0x000f000f000f000f#64
  let c := (b <<< 9 ||| b <<< 3) ||| (b <<< 6 ||| b)
  let d := c &&& 0x1111111111111111#64
  let e := d ||| d <<< 2
  e ||| e <<< 1

theorem widenCircuit_eq_bitwise (x : BitVec 16) : widenCircuit x = widenBitwise x := by
  have hm (a : BitVec 64) : a * 0x1000001000#64 = a <<< 12 + a <<< 36 := by
    change a * (BitVec.twoPow 64 12 + BitVec.twoPow 64 36) = _
    rw [BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft, BitVec.mul_twoPow_eq_shiftLeft]
  have ha : x.setWidth 64 <<< 12 + x.setWidth 64 <<< 36 =
      x.setWidth 64 <<< 12 ||| x.setWidth 64 <<< 36 := by
    simpa only [setWidth16_mask] using
      masked_shift_add_eq_or (x.setWidth 64) (x.setWidth 64) 0xffff#64 0xffff#64 12 36
        (by decide +kernel)
  have hb (z : BitVec 64) :
      (z &&& 0x000f000f000f000f#64) <<< 9 + (z &&& 0x000f000f000f000f#64) <<< 3 =
      (z &&& 0x000f000f000f000f#64) <<< 9 ||| (z &&& 0x000f000f000f000f#64) <<< 3 :=
    masked_shift_add_eq_or z z _ _ 9 3 (by decide +kernel)
  have hd (z : BitVec 64) :
      (z &&& 0x1111111111111111#64) + (z &&& 0x1111111111111111#64) * 4#64 =
      (z &&& 0x1111111111111111#64) ||| (z &&& 0x1111111111111111#64) <<< 2 := by
    change _ + _ * BitVec.twoPow 64 2 = _
    rw [BitVec.mul_twoPow_eq_shiftLeft]
    exact masked_shift_add_self z _ 2 (by decide +kernel)
  have he (z : BitVec 64) :
      ((z &&& 0x1111111111111111#64) ||| (z &&& 0x1111111111111111#64) <<< 2) &&&
        0x5555555555555555#64 =
      (z &&& 0x1111111111111111#64) ||| (z &&& 0x1111111111111111#64) <<< 2 := by
    simp (config := { bitVecOfNat := false }) only [BitVec.shiftLeft_and_distrib,
      BitVec.and_or_distrib_right, BitVec.and_assoc]
    rfl
  have hf (z : BitVec 64) :
      let e := (z &&& 0x1111111111111111#64) ||| (z &&& 0x1111111111111111#64) <<< 2
      e + e * 2#64 = e ||| e <<< 1 := by
    dsimp only
    change _ + _ * BitVec.twoPow 64 1 = _
    rw [BitVec.mul_twoPow_eq_shiftLeft]
    simpa (config := { bitVecOfNat := false }) only [he] using masked_shift_add_self
      ((z &&& 0x1111111111111111#64) ||| (z &&& 0x1111111111111111#64) <<< 2)
      0x5555555555555555#64 1 (by decide +kernel)
  simp (config := { bitVecOfNat := false }) only [widenCircuit, hm, ha, hb, hd, hf, widenBitwise]

set_option maxHeartbeats 800000 in
theorem widenBitwise_eq_widenWord (x : BitVec 16) : widenBitwise x = widenWord x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_widenWord x ⟨i, hi⟩]
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [widenBitwise]

theorem widenCircuit_eq_widenWord (x : BitVec 16) : widenCircuit x = widenWord x :=
  (widenCircuit_eq_bitwise x).trans (widenBitwise_eq_widenWord x)

def projectWord (x : BitVec 64) (b : Fin 4) : BitVec 16 :=
  fromBits fun i ↦ x.getLsbD (4 * i.val + b.val)

theorem getLsbD_projectWord (x : BitVec 64) (b : Fin 4) (i : Fin 16) :
    (projectWord x b).getLsbD i.val = x.getLsbD (4 * i.val + b.val) :=
  getLsbD_fromBits _ _

theorem projectWord_widenWord (x : BitVec 16) (b : Fin 4) :
    projectWord (widenWord x) b = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_projectWord _ b ⟨i, hi⟩, getLsbD_widenWord x ⟨4 * i + b.val, by omega⟩]
  congr 1
  change (4 * i + b.val) / 4 = i
  omega

def widenPlanes (x : Planes16) : Fixslice.Planes := fun p ↦ widenWord (x p)

def projectPlanes (x : Fixslice.Planes) (b : Fin 4) : Planes16 := fun p ↦ projectWord (x p) b

theorem projectPlanes_widenPlanes (x : Planes16) (b : Fin 4) :
    projectPlanes (widenPlanes x) b = x := by
  funext p
  exact projectWord_widenWord (x p) b

theorem widenPlanes_injective {x y : Planes16} (h : widenPlanes x = widenPlanes y) :
    x = y := by
  have he := congrArg (fun a ↦ projectPlanes a 0) h
  simpa only [projectPlanes_widenPlanes] using he

theorem widenPlanes_encode (x : Block) :
    widenPlanes (encode x) = Fixslice.encode (Fixslice.broadcast x) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (widenWord (encode x p)).getLsbD i = _
  rw [getLsbD_widenWord _ ⟨i, hi⟩, getLsbD_encode x p ⟨i / 4, by omega⟩,
    Fixslice.getLsbD_encode _ p ⟨i, hi⟩]
  congr 2
  apply Fin.ext
  simp only [transposeIndex]
  omega

theorem projectPlanes_encode (x : Fixslice.Blocks) (b : Fin 4) :
    projectPlanes (Fixslice.encode x) b = encode (x b) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (projectWord (Fixslice.encode x p) b).getLsbD i = _
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_encode _ p ⟨4 * i + b.val, by omega⟩, getLsbD_encode _ p ⟨i, hi⟩]
  have hb : (4 * i + b.val) % 4 = b.val := by omega
  have hj : 4 * ((4 * i + b.val) / 4 % 4) + (4 * i + b.val) / 16 =
      4 * (i % 4) + i / 4 := by omega
  simp only [hb, hj, transposeIndex]

theorem widenPlanes_xorPlanes (x y : Planes16) :
    widenPlanes (xorPlanes x y) = Fixslice.xorPlanes (widenPlanes x) (widenPlanes y) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (widenWord (x p ^^^ y p)).getLsbD i =
    (widenWord (x p) ^^^ widenWord (y p)).getLsbD i
  simp only [BitVec.getLsbD_xor, getLsbD_widenWord _ ⟨i, hi⟩]

set_option maxHeartbeats 800000 in
theorem widenPlanes_subBytes (x : Planes16) :
    widenPlanes (subBytes x) = Fixslice.subBytes (widenPlanes x) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (widenWord (Fixslice.subBytesCircuit x p)).getLsbD i =
    (Fixslice.subBytesCircuit (widenPlanes x) p).getLsbD i
  rw [getLsbD_widenWord _ ⟨i, hi⟩, getLsbD_subBytesCircuit, getLsbD_subBytesCircuit]
  simp only [widenPlanes, getLsbD_widenWord _ ⟨i, hi⟩]

end AesGcm.Proofs.Machine.Fixslice16
