import K256.Proofs.Common.Field.Repr
import K256.Proofs.Common.Field.WordOps

namespace K256.Proofs.Common.Field
open X86Proofs

namespace Multiply

abbrev Wide := Word × Word

def wideMul (a b : Word) : Wide := (a * b, (mulResult a b).2)

def wideAdd (a b : Wide) : Wide :=
  (a.1 + b.1, a.2 + b.2 + BitVec.ofNat 64 (addSpec a.1 b.1).2.CF.toNat)

def wideAddRev (a b : Wide) : Wide :=
  (a.1 + b.1, b.2 + a.2 + BitVec.ofNat 64 (addSpec a.1 b.1).2.CF.toNat)

def ofWord (a : Word) : Wide := (a, 0)

def high52 (a : Wide) : Word := shldResult 12 a.2 a.1

def low52 (a : Wide) : Word := a.1 &&& 0xfffffffffffff

def low48 (a : Wide) : Word := a.1 &&& 0xffffffffffff

def combine56 (a b : Wide) : Word :=
  a.1 <<< 4 &&& (72057594037927920 : Word) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (b.1 >>> 48) &&& 15)

end Multiply

open Multiply in
def mulWords (a b : Limbs) : Limbs :=
  let p (i j : Fin 5) := wideMul a[i] b[j]
  let c₈ := p 4 4
  let c₃ := wideAdd (wideAdd (wideAdd (p 0 3) (p 1 2)) (p 2 1)) (p 3 0)
  let d₃ := wideAdd c₃ (wideMul (low52 c₈) 0x1000003d10)
  let c₄ := wideAdd (wideAdd (wideAdd (wideAdd (p 0 4) (p 1 3)) (p 2 2)) (p 3 1)) (p 4 0)
  let d₄ := wideAdd (wideAdd c₄ (wideMul (high52 c₈) 0x1000003d10)) (ofWord (high52 d₃))
  let c₅ := wideAdd (wideAdd (wideAddRev (p 1 4) (p 2 3)) (p 3 2)) (p 4 1)
  let d₅ := wideAdd c₅ (ofWord (high52 d₄))
  let r₀ := wideAdd (wideMul (combine56 d₅ d₄) 0x1000003d1) (p 0 0)
  let c₆ := wideAdd (wideAddRev (p 2 4) (p 3 3)) (p 4 2)
  let d₆ := wideAdd c₆ (ofWord (high52 d₅))
  let c₁ := wideAdd (p 0 1) (p 1 0)
  let r₁ := wideAdd (wideAdd c₁ (wideMul (low52 d₆) 0x1000003d10)) (ofWord (high52 r₀))
  let c₇ := wideAddRev (p 3 4) (p 4 3)
  let d₇ := wideAdd c₇ (ofWord (high52 d₆))
  let c₂ := wideAdd (wideAdd (p 0 2) (p 1 1)) (p 2 0)
  let r₂ := wideAdd (wideAdd c₂ (wideMul (low52 d₇) 0x1000003d10)) (ofWord (high52 r₁))
  let r₃ := wideAdd (wideAddRev (ofWord (low52 d₃)) (wideMul (high52 d₇) 0x1000003d10))
    (ofWord (high52 r₂))
  #v[low52 r₀, low52 r₁, low52 r₂, low52 r₃, low48 d₄ + high52 r₃]

end K256.Proofs.Common.Field
