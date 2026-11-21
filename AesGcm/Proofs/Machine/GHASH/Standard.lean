import Std
import Standards.NIST.GCM.Multiplication

namespace AesGcm.Proofs.Machine.GHASH

def toGcmBits (x : BitVec 128) : Vector Bool 128 := Vector.ofFn (fun i => x.getLsbD i.val)

def gcmDouble (x : BitVec 128) : BitVec 128 :=
  if x.getLsbD 127 then (x <<< (1 : Nat)) ^^^ 0x87#128 else x <<< (1 : Nat)

def gcmStep (x : BitVec 128) (p : BitVec 128 × BitVec 128) (i : Fin 128) :
    BitVec 128 × BitVec 128 :=
  (if x.getLsbD i.val then p.1 ^^^ p.2 else p.1, gcmDouble p.2)

def standardStep (x : Vector Bool 128) (p : Vector Bool 128 × Vector Bool 128) (i : Fin 128) :
    Vector Bool 128 × Vector Bool 128 :=
  (if x[i] then Standards.NIST.GCM.xor p.1 p.2 else p.1,
    if Standards.NIST.GCM.LSB 1 p.2 = #v[false] then Standards.NIST.GCM.rightShift p.2
    else Standards.NIST.GCM.xor (Standards.NIST.GCM.rightShift p.2) Standards.NIST.GCM.R)

def toGcmState (p : BitVec 128 × BitVec 128) : Vector Bool 128 × Vector Bool 128 :=
  (toGcmBits p.1, toGcmBits p.2)

def gcmMul128 (x y : BitVec 128) : BitVec 128 :=
  ((List.finRange 128).foldl (gcmStep x) (0#128, y)).1

theorem toGcmBits_zero : toGcmBits (0#128) = Standards.NIST.GCM.zeros 128 := by
  apply Vector.ext
  intro i hi
  simp [toGcmBits, Standards.NIST.GCM.zeros]

theorem toGcmBits_xor (x y : BitVec 128) :
    toGcmBits (x ^^^ y) = Standards.NIST.GCM.xor (toGcmBits x) (toGcmBits y) := by
  apply Vector.ext
  intro i hi
  simp [toGcmBits, Standards.NIST.GCM.xor]

theorem toGcmBits_shift (x : BitVec 128) :
    toGcmBits (x <<< (1 : Nat)) = Standards.NIST.GCM.rightShift (toGcmBits x) := by
  apply Vector.ext
  intro i hi
  simp only [toGcmBits, Standards.NIST.GCM.rightShift, Standards.NIST.GCM.MSB,
    Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_append]
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h : i = 0
  · subst i; simp
  · have hi' : ¬ i < 1 := by omega
    simp [hi, hi']

theorem toGcmBits_reduction : toGcmBits (0x87#128) = Standards.NIST.GCM.R := by
  decide +kernel

theorem toGcmBits_lsb (x : BitVec 128) :
    Standards.NIST.GCM.LSB 1 (toGcmBits x) = #v[false] ↔ x.getLsbD 127 = false := by
  constructor
  · intro h
    have he := congrArg (fun v : Vector Bool 1 => v[0]) h
    simpa [Standards.NIST.GCM.LSB, toGcmBits] using he
  · intro h
    apply Vector.ext
    intro i hi
    have : i = 0 := by omega
    subst i
    simpa [Standards.NIST.GCM.LSB, toGcmBits] using h

theorem toGcmBits_double (x : BitVec 128) :
    toGcmBits (gcmDouble x) =
      if Standards.NIST.GCM.LSB 1 (toGcmBits x) = #v[false]
      then Standards.NIST.GCM.rightShift (toGcmBits x)
      else Standards.NIST.GCM.xor (Standards.NIST.GCM.rightShift (toGcmBits x)) Standards.NIST.GCM.R := by
  simp only [toGcmBits_lsb]
  cases h : x.getLsbD 127 <;>
    simp only [gcmDouble, h, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
      toGcmBits_xor, toGcmBits_shift, toGcmBits_reduction]

theorem toGcmBits_conditional (x z v : BitVec 128) (i : Fin 128) :
    (if (toGcmBits x)[i] then Standards.NIST.GCM.xor (toGcmBits z) (toGcmBits v)
      else toGcmBits z) = toGcmBits (if x.getLsbD i.val then z ^^^ v else z) := by
  have hb : (toGcmBits x)[i] = x.getLsbD i.val := by simp [toGcmBits]
  rw [hb]
  split <;> simp only [toGcmBits_xor]

theorem toGcmState_step (x : BitVec 128) (p : BitVec 128 × BitVec 128) (i : Fin 128) :
    standardStep (toGcmBits x) (toGcmState p) i = toGcmState (gcmStep x p i) := by
  dsimp only [standardStep, toGcmState, gcmStep]
  apply Prod.ext
  · dsimp only
    exact toGcmBits_conditional x p.1 p.2 i
  · dsimp only
    exact (toGcmBits_double p.2).symm

theorem gcmMul128_eq_standard (x y : BitVec 128) :
    toGcmBits (gcmMul128 x y) = Standards.NIST.GCM.mul (toGcmBits x) (toGcmBits y) := by
  have h := List.foldl_hom (f := toGcmState) (g₁ := gcmStep x)
    (g₂ := standardStep (toGcmBits x)) (l := List.finRange 128) (init := (0#128, y))
    (toGcmState_step x)
  have hp := congrArg Prod.fst h
  simp only [toGcmState, toGcmBits_zero] at hp
  simp only [Standards.NIST.GCM.mul, List.forIn_pure_yield_eq_foldl]
  exact hp.symm

theorem reverse_ushiftRight_one {w : Nat} (x : BitVec w) :
    (x >>> (1 : Nat)).reverse = x.reverse <<< (1 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases hz : i = 0
  · subst i
    have he : 1 + (w - 1) = w := by omega
    simp [he]
  · have h1 : ¬i < 1 := by omega
    have h2 : i - 1 < w := by omega
    have he : 1 + (w - 1 - i) = w - 1 - (i - 1) := by omega
    simp [h1, h2, he]

theorem reverse_xor {w : Nat} (x y : BitVec w) :
    (x ^^^ y).reverse = x.reverse ^^^ y.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_xor,
    hi, decide_true, Bool.true_and]

def polyvalDivide (x : BitVec 128) : BitVec 128 :=
  (x >>> (1 : Nat)) ^^^ (if x.getLsbD 0 then 0xe1000000000000000000000000000000#128 else 0)

theorem polyvalDivide_reverse (x : BitVec 128) :
    (polyvalDivide x).reverse = gcmDouble x.reverse := by
  have hb : x.reverse.getLsbD 127 = x.getLsbD 0 := by
    simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, Nat.reduceSub,
      Nat.reduceLT, decide_true, Bool.true_and]
  have hk : (0xe1000000000000000000000000000000#128).reverse = 0x87#128 := by decide +kernel
  simp only [polyvalDivide, gcmDouble, hb, reverse_xor, reverse_ushiftRight_one]
  have hz : (0#128).reverse = 0#128 := by decide +kernel
  cases x.getLsbD 0 <;> simp [hk, hz]

end AesGcm.Proofs.Machine.GHASH
