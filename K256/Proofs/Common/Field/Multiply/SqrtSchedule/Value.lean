import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Words
import K256.Proofs.Common.Field.Multiply

namespace K256.Proofs.Common.Field.Multiply.SqrtSchedule
open X86Proofs

macro "sqrt_product_words" : tactic =>
  `(tactic| simp only [wideAddRev_eq, wideAdd_assoc, wideAdd_left_comm, wideAdd_comm, wideMul_comm])

def productCoefficients (p : Fin 5 → Fin 5 → Wide) : Coefficients :=
  ⟨p 0 0,
   wideAdd (p 0 1) (p 1 0),
   wideAdd (wideAdd (p 0 2) (p 1 1)) (p 2 0),
   wideAdd (wideAdd (wideAdd (p 0 3) (p 1 2)) (p 2 1)) (p 3 0),
   wideAdd (wideAdd (wideAdd (wideAdd (p 0 4) (p 1 3)) (p 2 2)) (p 3 1)) (p 4 0),
   wideAdd (wideAdd (wideAddRev (p 1 4) (p 2 3)) (p 3 2)) (p 4 1),
   wideAdd (wideAddRev (p 2 4) (p 3 3)) (p 4 2),
   wideAddRev (p 3 4) (p 4 3), p 4 4⟩

private theorem convolution_eq (s : Schedule) (p : Fin 5 → Fin 5 → Wide) :
    convolution s p = productCoefficients p := by
  cases s <;> simp only [convolution, productCoefficients, addHigh] <;> sqrt_product_words

private theorem addHigh_eq (s : Schedule) : addHigh s = wideAdd := by
  cases s <;> funext x y <;> simp only [addHigh, wideAddRev_eq]

private theorem addPartial_eq (s : Schedule) : addPartial s = wideAdd := by
  cases s <;> funext x y <;> simp only [addPartial, wideAddRev_eq, wideAdd_comm]

private theorem addDiagonalThree_eq (s : Schedule) : addDiagonalThree s = wideAdd := by
  cases s <;> funext x y <;> simp only [addDiagonalThree, addHigh_eq, wideAdd_comm]

private theorem addFinalCarry_eq (s : Schedule) : addFinalCarry s = wideAddRev := by
  cases s <;> funext x y <;> simp only [addFinalCarry, wideAddRev_eq, wideAdd_comm]

theorem reduce_productCoefficients (a b : Limbs) :
    reduceWords wideAdd wideAdd wideAdd wideAddRev
      (productCoefficients (fun i j : Fin 5 => wideMul b[i] a[j]))
      (wideMul (high52 (wideMul b[4] a[4])) 0x1000003d10) = Field.mulWords b a := by
  rfl

private theorem reduce_schedule (s : Schedule) (p : Fin 5 → Fin 5 → Wide)
    (hz : (p 4 4).2 >>> 52 = 0) :
    reduceWords (addDiagonalThree s) (addPartial s) (addHigh s) (addFinalCarry s)
      (convolution s p) (scaleHigh (p 4 4) (match s with
        | .third => shrdResult 52 (p 4 4).1 (p 4 4).2
        | _ => high52 (p 4 4))) =
    reduceWords wideAdd wideAdd wideAdd wideAddRev (productCoefficients p)
      (wideMul (high52 (p 4 4)) 0x1000003d10) := by
  have hlo (q : Wide) : (match s with
    | .third => shrdResult 52 q.1 q.2
    | _ => high52 q) = high52 q := by
    cases s with
    | third => exact shrd52_eq q.1 q.2
    | fifth | other => rfl
  rw [addDiagonalThree_eq, addPartial_eq, addHigh_eq, addFinalCarry_eq, convolution_eq,
    hlo, scaleHigh_eq hz]

theorem mulWords_eq (s : Schedule) (a b : Limbs)
    (h : b[4].toNat * a[4].toNat < 2^116) :
    mulWords s a b = Field.mulWords b a := by
  exact (reduce_schedule s (fun i j : Fin 5 => wideMul b[i] a[j])
    (top_product_shift_zero h)).trans (reduce_productCoefficients a b)

theorem mulWords_repr (s : Schedule) (a b : Limbs) (x y : Fin modulus)
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    FieldRepr (mulWords s a b) (y * x) 1 := by
  rw [mulWords_eq s a b (top_product_lt hb ha)]
  exact Field.mulWords_repr b a y x hb ha

end K256.Proofs.Common.Field.Multiply.SqrtSchedule
