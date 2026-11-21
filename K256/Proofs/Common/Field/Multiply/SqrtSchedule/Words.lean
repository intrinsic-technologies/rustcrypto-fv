import K256.Proofs.Common.Field.Multiply.SqrtSchedule.High

namespace K256.Proofs.Common.Field.Multiply.SqrtSchedule
open X86Proofs

inductive Schedule where
  | third
  | fifth
  | other
  deriving DecidableEq

def addHigh : Schedule → Wide → Wide → Wide
  | .fifth => wideAddRev
  | _ => wideAdd

def addPartial : Schedule → Wide → Wide → Wide
  | .fifth, sum, term => wideAddRev term sum
  | _, sum, term => wideAdd sum term

def addDiagonalThree : Schedule → Wide → Wide → Wide
  | .third, sum, term => wideAdd sum term
  | s, sum, term => addHigh s term sum

def addFinalCarry : Schedule → Wide → Wide → Wide
  | .fifth, sum, term => wideAdd term sum
  | _, sum, term => wideAddRev sum term

structure Coefficients where
  c0 : Wide
  c1 : Wide
  c2 : Wide
  c3 : Wide
  c4 : Wide
  c5 : Wide
  c6 : Wide
  c7 : Wide
  c8 : Wide

def convolution (s : Schedule) (p : Fin 5 → Fin 5 → Wide) : Coefficients :=
  let c₃ := match s with
    | .third => wideAdd (wideAdd (wideAdd (p 0 3) (p 1 2)) (p 2 1)) (p 3 0)
    | _ => addHigh s (p 0 3) (addHigh s (p 1 2) (addHigh s (p 2 1) (p 3 0)))
  let c₄ := match s with
    | .third => wideAdd (wideAdd (wideAdd (wideAdd (p 1 3) (p 2 2)) (p 0 4)) (p 3 1)) (p 4 0)
    | _ => wideAdd (wideAdd (wideAdd (wideAdd (p 3 1) (p 4 0)) (p 2 2)) (p 1 3)) (p 0 4)
  let c₅ := match s with
    | .third => wideAdd (wideAdd (wideAddRev (p 1 4) (p 2 3)) (p 3 2)) (p 4 1)
    | _ => wideAddRev (p 1 4) (wideAdd (wideAdd (p 3 2) (p 4 1)) (p 2 3))
  let c₆ := match s with
    | .third => wideAdd (wideAddRev (p 2 4) (p 3 3)) (p 4 2)
    | _ => wideAddRev (p 2 4) (wideAdd (p 3 3) (p 4 2))
  let c₂ := match s with
    | .third => wideAdd (wideAdd (p 0 2) (p 1 1)) (p 2 0)
    | _ => wideAdd (wideAdd (p 1 1) (p 2 0)) (p 0 2)
  ⟨p 0 0, wideAdd (p 0 1) (p 1 0), c₂, c₃, c₄, c₅, c₆, wideAddRev (p 3 4) (p 4 3), p 4 4⟩

def reduceWords (add₃ add₄ add₀ addLast : Wide → Wide → Wide)
    (c : Coefficients) (scaledTop : Wide) : Limbs :=
  let d₃ := add₃ c.c3 (wideMul (low52 c.c8) 0x1000003d10)
  let d₄ := wideAdd (add₄ c.c4 scaledTop) (ofWord (high52 d₃))
  let d₅ := wideAdd c.c5 (ofWord (high52 d₄))
  let r₀ := add₀ (wideMul (combine56 d₅ d₄) 0x1000003d1) c.c0
  let d₆ := wideAdd c.c6 (ofWord (high52 d₅))
  let r₁ := wideAdd (add₄ c.c1 (wideMul (low52 d₆) 0x1000003d10)) (ofWord (high52 r₀))
  let d₇ := wideAdd c.c7 (ofWord (high52 d₆))
  let r₂ := wideAdd (add₄ c.c2 (wideMul (low52 d₇) 0x1000003d10)) (ofWord (high52 r₁))
  let r₃ := wideAdd (addLast (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10)) (ofWord (high52 r₂))
  #v[low52 r₀, low52 r₁, low52 r₂, low52 r₃, low48 d₄ + high52 r₃]

def mulWords (s : Schedule) (a b : Limbs) : Limbs :=
  let p (i j : Fin 5) := wideMul b[i] a[j]
  let c₈ := p 4 4
  let lo := match s with
    | .third => shrdResult 52 c₈.1 c₈.2
    | _ => high52 c₈
  reduceWords (addDiagonalThree s) (addPartial s) (addHigh s) (addFinalCarry s)
    (convolution s p) (scaleHigh c₈ lo)

end K256.Proofs.Common.Field.Multiply.SqrtSchedule
