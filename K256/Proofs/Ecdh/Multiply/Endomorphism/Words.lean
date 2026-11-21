import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Value

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism

open X86Proofs K256.Proofs.Common.Field K256.Proofs.Common.Field.Multiply

def betaLimbs : Limbs := #v[0x96c28719501ee, 0x7512f58995c13, 0xc3434e99cf049,
  0x7106e64479ea, 0x7ae96a2b657c]

def betaMulWords (a : Limbs) : Limbs :=
  let p (i j : Fin 5) := wideMul a[i] betaLimbs[j]
  let c₈ := p 4 4
  let c₃ := wideAdd (p 3 0) (wideAdd (p 2 1) (wideAdd (p 1 2) (p 0 3)))
  let d₃ := wideAdd (wideMul (0xffffffffffffc &&& c₈.1) 0x1000003d10) c₃
  let c₄ := wideAdd (wideAdd (wideAdd (wideAdd (p 1 3) (p 0 4)) (p 2 2)) (p 3 1)) (p 4 0)
  let d₄ := wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10)) (ofWord (high52 d₃))
  let c₅ := wideAddRev (p 4 1) (wideAdd (wideAdd (p 2 3) (p 1 4)) (p 3 2))
  let d₅ := wideAdd c₅ (ofWord (high52 d₄))
  let r₀ := wideAdd (wideMul (combine56 d₅ d₄) 0x1000003d1) (p 0 0)
  let c₆ := wideAddRev (p 4 2) (wideAdd (p 3 3) (p 2 4))
  let d₆ := wideAdd c₆ (ofWord (high52 d₅))
  let c₁ := wideAdd (p 1 0) (p 0 1)
  let r₁ := wideAdd (wideAdd c₁ (wideMul (low52 d₆) 0x1000003d10)) (high52 r₀, r₀.2 >>> 52)
  let c₇ := wideAddRev (p 4 3) (p 3 4)
  let d₇ := wideAdd c₇ (high52 d₆, d₆.2 >>> 52)
  let c₂ := wideAdd (wideAdd (p 1 1) (p 0 2)) (p 2 0)
  let r₂ := wideAdd (wideAdd c₂ (wideMul (low52 d₇) 0x1000003d10)) (ofWord (high52 r₁))
  let r₃ := wideAdd (wideAddRev (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10))
    (ofWord (high52 r₂))
  #v[low52 r₀, low52 r₁, low52 r₂, 0xfffffffffffff &&& r₃.1, (0xffffffffffff &&& d₄.1) + high52 r₃]

end K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
