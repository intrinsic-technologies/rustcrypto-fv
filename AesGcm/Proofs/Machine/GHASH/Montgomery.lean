import AesGcm.Proofs.Machine.GHASH.Standard
import AesGcm.Proofs.Machine.GHASH.Reduction
import AesGcm.Proofs.Machine.GHASH.WideProduct

namespace AesGcm.Proofs.Machine.GHASH

def polyvalMulX (x : BitVec 128) : BitVec 128 :=
  (x <<< (1 : Nat)) ^^^ (if x.getLsbD 127 then 0xc2000000000000000000000000000001#128 else 0)

theorem polyvalMulX_low (x : BitVec 128) : (polyvalMulX x).getLsbD 0 = x.getLsbD 127 := by
  simp only [polyvalMulX, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
  cases x.getLsbD 127 <;> simp

theorem shiftLeft_half_restore (x : BitVec 128) :
    ((x <<< (1 : Nat)) >>> (1 : Nat)) ^^^
      (if x.getLsbD 127 then BitVec.twoPow 128 127 else 0) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases he : i = 127
  · subst i
    cases x.getLsbD 127 <;> simp
  · have hs : 1 + i < 128 := by omega
    cases x.getLsbD 127 <;> simp [BitVec.getLsbD_twoPow, hs, Ne.symm he]

theorem polyvalDivide_mulX (x : BitVec 128) : polyvalDivide (polyvalMulX x) = x := by
  rw [polyvalDivide, polyvalMulX_low]
  simp only [polyvalMulX, BitVec.ushiftRight_xor_distrib]
  have hk : (0xc2000000000000000000000000000001#128 >>> (1 : Nat)) ^^^
      0xe1000000000000000000000000000000#128 = BitVec.twoPow 128 127 := by decide +kernel
  have h := shiftLeft_half_restore x
  cases hb : x.getLsbD 127
  · simpa only [hb, Bool.false_eq_true, ite_false, BitVec.ofNat_eq_ofNat,
      BitVec.zero_ushiftRight, BitVec.xor_zero] using h
  · simp only [ite_true]
    rw [BitVec.xor_assoc, hk]
    simpa only [hb, ite_true] using h

theorem polyvalStep_zero : polyvalStep (0#256) = 0#256 := by rfl

theorem polyvalStep_xor (x y : BitVec 256) :
    polyvalStep (x ^^^ y) = polyvalStep x ^^^ polyvalStep y := by
  simp only [polyvalStep, BitVec.ushiftRight_xor_distrib, BitVec.getLsbD_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases x.getLsbD 0 <;> cases y.getLsbD 0 <;>
    simp [BitVec.getLsbD_xor, Bool.xor_comm, Bool.xor_left_comm]

theorem polyvalSteps_zero (n : Nat) : polyvalSteps n (0#256) = 0#256 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [polyvalSteps, ih, polyvalStep_zero]

theorem polyvalSteps_xor (n : Nat) (x y : BitVec 256) :
    polyvalSteps n (x ^^^ y) = polyvalSteps n x ^^^ polyvalSteps n y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [polyvalSteps, ih, polyvalStep_xor]; rfl

theorem polyvalStep_embed (x : BitVec 128) :
    polyvalStep (x.setWidth 256) = (polyvalDivide x).setWidth 256 := by
  simp only [polyvalStep, polyvalDivide, BitVec.getLsbD_setWidth, Nat.reduceLT,
    decide_true, Bool.true_and, BitVec.setWidth_xor, BitVec.setWidth_ushiftRight (by decide : 128 ≤ 256)]
  cases x.getLsbD 0 <;> rfl

theorem polyvalSteps_embed (n : Nat) (x : BitVec 128) :
    polyvalSteps n (x.setWidth 256) = (Nat.repeat polyvalDivide n x).setWidth 256 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [polyvalSteps, ih, polyvalStep_embed]; rfl

theorem polyvalDivide_repeat_reverse (n : Nat) (x : BitVec 128) :
    (Nat.repeat polyvalDivide n x).reverse = Nat.repeat gcmDouble n x.reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, polyvalDivide_reverse, ih]

theorem polyvalSteps_succ_first (n : Nat) (x : BitVec 256) :
    polyvalSteps (n + 1) x = polyvalSteps n (polyvalStep x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change polyvalStep (polyvalSteps (n + 1) x) = polyvalStep (polyvalSteps n (polyvalStep x))
    rw [ih]

theorem polyvalStep_shift (x : BitVec 128) (n : Nat) (hn : n < 128) :
    polyvalStep (x.setWidth 256 <<< (n + 1)) = x.setWidth 256 <<< n := by
  have h := shiftedPrefix_half (129 + n) 128 (x.setWidth 256) (by omega) (by omega)
  have h1 : 129 + n - 128 = n + 1 := by omega
  have h2 : 129 + n - (128 + 1) = n := by omega
  simp only [polyvalStep, BitVec.getLsbD_shiftLeft,
    Nat.zero_lt_succ, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  simpa [shiftedPrefix, truncateBits, h1, h2] using h

theorem polyvalSteps_shift (x : BitVec 128) (n : Nat) (hn : n ≤ 128) :
    polyvalSteps n (x.setWidth 256 <<< n) = x.setWidth 256 := by
  induction n with
  | zero => simp [polyvalSteps]
  | succ n ih =>
    rw [polyvalSteps_succ_first, polyvalStep_shift x n (by omega), ih (by omega)]

theorem repeat_succ_first {α : Type} (f : α → α) (n : Nat) (x : α) :
    Nat.repeat f (n + 1) x = Nat.repeat f n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (Nat.repeat f (n + 1) x) = f (Nat.repeat f n (f x))
    rw [ih]

def gcmReduce (x : BitVec 256) : BitVec 128 := ((polyvalSteps 128 x).setWidth 128).reverse

theorem gcmReduce_term (h : BitVec 128) (i : Nat) (hi : i < 128) :
    gcmReduce ((polyvalMulX h).setWidth 256 <<< i) =
      Nat.repeat gcmDouble (127 - i) h.reverse := by
  unfold gcmReduce
  have hs := polyvalSteps_add i (128 - i) ((polyvalMulX h).setWidth 256 <<< i)
  rw [show i + (128 - i) = 128 from by omega,
    polyvalSteps_shift (polyvalMulX h) i (by omega)] at hs
  rw [hs, polyvalSteps_embed]
  simp only [BitVec.setWidth_setWidth_of_le _ (show 128 ≤ 256 from by decide), BitVec.setWidth_eq]
  rw [show 128 - i = (127 - i) + 1 from by omega, repeat_succ_first, polyvalDivide_mulX,
    polyvalDivide_repeat_reverse]

theorem gcmReduce_zero : gcmReduce (0#256) = 0#128 := by
  rw [gcmReduce, polyvalSteps_zero]
  decide +kernel

theorem gcmReduce_xor (x y : BitVec 256) :
    gcmReduce (x ^^^ y) = gcmReduce x ^^^ gcmReduce y := by
  simp only [gcmReduce, polyvalSteps_xor, BitVec.setWidth_xor, reverse_xor]

def wideMul128 (x y : BitVec 128) : BitVec 256 :=
  xorSum ((List.range 128).map (fun i => if x.getLsbD i then y.setWidth 256 <<< i else 0))

theorem gcmReduce_wideMul128_series (x h : BitVec 128) :
    gcmReduce (wideMul128 x (polyvalMulX h)) =
      xorSum ((List.range 128).map (fun i =>
        if x.getLsbD i then Nat.repeat gcmDouble (127 - i) h.reverse else 0)) := by
  rw [wideMul128, ← xorSum_map_hom gcmReduce gcmReduce_zero gcmReduce_xor, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < 128 := List.mem_range.mp hi
  change gcmReduce (if x.getLsbD i then (polyvalMulX h).setWidth 256 <<< i else 0) = _
  cases x.getLsbD i
  · exact gcmReduce_zero
  · exact gcmReduce_term h i hi'

def gcmNatStep (x : BitVec 128) (p : BitVec 128 × BitVec 128) (i : Nat) :
    BitVec 128 × BitVec 128 :=
  (if x.getLsbD i then p.1 ^^^ p.2 else p.1, gcmDouble p.2)

theorem gcmFold_range (x y : BitVec 128) (n : Nat) :
    (List.range n).foldl (gcmNatStep x) (0#128, y) =
      (xorSum ((List.range n).map (fun i =>
        if x.getLsbD i then Nat.repeat gcmDouble i y else 0)), Nat.repeat gcmDouble n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.map_append, xorSum_append]
    cases h : x.getLsbD n <;> simp [gcmNatStep, xorSum, Nat.repeat, h]

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem gcmMul128_eq_series (x y : BitVec 128) :
    gcmMul128 x y = xorSum ((List.range 128).map (fun i =>
      if x.getLsbD i then Nat.repeat gcmDouble i y else 0)) := by
  unfold gcmMul128
  change ((List.finRange 128).foldl (fun p i => gcmNatStep x p i.val) (0#128, y)).1 = _
  rw [← List.foldl_map, map_val_finRange, gcmFold_range]

theorem gcmReduce_wideMul128 (x h : BitVec 128) :
    gcmReduce (wideMul128 x (polyvalMulX h)) = gcmMul128 x.reverse h.reverse := by
  rw [gcmReduce_wideMul128_series, gcmMul128_eq_series]
  let f := fun i => if x.reverse.getLsbD i then Nat.repeat gcmDouble i h.reverse else 0#128
  have hm : (List.range 128).map (fun i => 127 - i) = (List.range 128).reverse := by decide +kernel
  have he : (List.range 128).map (fun i =>
      if x.getLsbD i then Nat.repeat gcmDouble (127 - i) h.reverse else 0#128) =
        ((List.range 128).map (fun i => 127 - i)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < 128 := List.mem_range.mp hi
    have hb : x.reverse.getLsbD (127 - i) = x.getLsbD i := by
      simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
        show 127 - i < 128 from by omega, decide_true, Bool.true_and,
        show 128 - 1 - (127 - i) = i from by omega]
    change (if x.getLsbD i then Nat.repeat gcmDouble (127 - i) h.reverse else 0#128) =
      (if x.reverse.getLsbD (127 - i) then Nat.repeat gcmDouble (127 - i) h.reverse else 0#128)
    rw [hb]
  change xorSum ((List.range 128).map (fun i =>
    if x.getLsbD i then Nat.repeat gcmDouble (127 - i) h.reverse else 0#128)) =
      xorSum ((List.range 128).map f)
  rw [he, hm, List.map_reverse, xorSum_reverse]

theorem gcmReduce_wideMul128_eq_standard (x h : BitVec 128) :
    toGcmBits (gcmReduce (wideMul128 x (polyvalMulX h))) =
      Standards.NIST.GCM.mul (toGcmBits x.reverse) (toGcmBits h.reverse) := by
  rw [gcmReduce_wideMul128, gcmMul128_eq_standard]

end AesGcm.Proofs.Machine.GHASH
