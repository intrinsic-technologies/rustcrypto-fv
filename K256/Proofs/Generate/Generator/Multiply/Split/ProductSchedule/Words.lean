import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Field.Multiply.Bounds
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule

open K256.Proofs.Common.Field X86Proofs

abbrev Word := BitVec 64
abbrev Wide := Word × Word

def bit (c : Bool) : Word := BitVec.ofNat 64 c.toNat

structure Column where
  lo : Word
  mid : Word
  hi : Word

def addWide (x y : Wide) : Wide × Bool :=
  let c := (addSpec x.1 y.1).2.CF
  ((x.1 + y.1, x.2 + y.2 + bit c), (adcSpec c x.2 y.2).2.CF)

def first (carry : Word) (p q : Wide) : Column :=
  let lo := carry + p.1
  let c := (addSpec lo q.1).2.CF
  let hi := q.2 + bit c
  let d := (addSpec carry p.1).2.CF
  ⟨q.1 + lo, hi + p.2 + bit d, bit (adcSpec d hi p.2).2.CF⟩

def three (prev : Column) (p q r : Wide) : Column :=
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  let c := addWide b.1 r
  ⟨c.1.1, c.1.2, bit b.2 + bit a.2 + bit c.2⟩

def four (prev : Column) (p q r s : Wide) : Column :=
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  let c := addWide b.1 r
  let d := addWide c.1 s
  ⟨d.1.1, d.1.2, bit c.2 + (bit b.2 + bit a.2) + bit d.2⟩

def last (prev : Column) (p q top : Wide) : Column :=
  let a := addWide (prev.mid, prev.hi) p
  let b := addWide a.1 q
  let hi := top.2 + bit a.2
  let c := (addSpec b.1.2 top.1).2.CF
  ⟨b.1.1, b.1.2 + top.1, bit b.2 + hi + bit c⟩

def machineProduct (a b : Vector Word 4) : Vector Word 8 :=
  let p (i j : Fin 4) := Multiply.wideMul b[j] a[i]
  let p₀ := p 0 0
  let c₁ := first p₀.2 (p 0 1) (p 1 0)
  let c₂ := three c₁ (p 0 2) (p 1 1) (p 2 0)
  let c₃ := four c₂ (p 0 3) (p 1 2) (p 2 1) (p 3 0)
  let c₄ := three c₃ (p 1 3) (p 2 2) (p 3 1)
  let c₅ := last c₄ (p 2 3) (p 3 2) (p 3 3)
  #v[p₀.1, c₁.lo, c₂.lo, c₃.lo, c₄.lo, c₅.lo, c₅.mid, c₅.hi]

end K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule
