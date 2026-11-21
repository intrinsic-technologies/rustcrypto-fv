import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Value

namespace K256.Proofs.Sec1.SqrtProducts

open X86Proofs Common.Field Common.Field.Multiply Common.Field.Multiply.SqrtSchedule

def secondCoefficients (p : Fin 5 → Fin 5 → Wide) : Coefficients :=
  ⟨p 0 0,
   wideAdd (p 1 0) (p 0 1),
   wideAdd (wideAdd (p 1 1) (p 0 2)) (p 2 0),
   wideAdd (p 3 0) (wideAdd (p 2 1) (wideAdd (p 1 2) (p 0 3))),
   wideAdd (wideAdd (wideAdd (wideAdd (p 1 3) (p 0 4)) (p 2 2)) (p 3 1)) (p 4 0),
   wideAddRev (p 4 1) (wideAdd (wideAdd (p 2 3) (p 1 4)) (p 3 2)),
   wideAddRev (p 4 2) (wideAdd (p 3 3) (p 2 4)), wideAddRev (p 4 3) (p 3 4), p 4 4⟩

def secondProduct (a b : Limbs) : Limbs :=
  let p (i j : Fin 5) := wideMul a[i] b[j]
  reduceWords (fun x y => wideAdd y x) wideAdd wideAdd wideAddRev (secondCoefficients p)
    (wideMul (high52 (p 4 4)) 0x1000003d10)

theorem secondProduct_eq_mulWords (a b : Limbs) : secondProduct a b = Common.Field.mulWords a b := by
  have coeff (p : Fin 5 → Fin 5 → Wide) : secondCoefficients p = productCoefficients p := by
    simp only [secondCoefficients, productCoefficients, wideAddRev_eq, wideAdd_comm]
  have flip : (fun x y => wideAdd y x) = wideAdd := funext fun x => funext fun y => wideAdd_comm y x
  simp only [secondProduct, coeff, flip]
  exact reduce_productCoefficients b a

end K256.Proofs.Sec1.SqrtProducts
