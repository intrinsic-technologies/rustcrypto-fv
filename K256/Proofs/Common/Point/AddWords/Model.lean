import K256.Proofs.Common.Field.Multiply.Words
import K256.Proofs.Sec1.Serialize.Normalize.Words

namespace K256.Proofs.Common.Point

open Field Sec1.Serialize.Normalize

structure PointWords where
  x : Limbs
  y : Limbs
  z : Limbs

namespace AddWords

def sum (a b : Limbs) : Limbs := Vector.ofFn fun i => a[i] + b[i]

def scale (n : Nat) (a : Limbs) : Limbs := Vector.ofFn fun i => a[i] * BitVec.ofNat 64 n

def modulusWords : Limbs := #v[0xffffefffffc2f, mask52, mask52, mask52, mask48]

def negate (m : Nat) (a : Limbs) : Limbs :=
  Vector.ofFn fun i => modulusWords[i] * BitVec.ofNat 64 (2 * (m + 1)) - a[i]

def weak (a : Limbs) : Limbs :=
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  #v[t0 &&& mask52, t1 &&& mask52, t2 &&& mask52, t3 &&& mask52, top t3 a[4]]

inductive ProductKind where
  | xx | yy | zz | xy | yz | xz | xLeft | xRight | yLeft | yRight | zLeft | zRight

def pairsWith (product : Limbs → Limbs → Limbs) (a b c d ac bd : Limbs) : Limbs :=
  sum (product (sum a b) (sum c d)) (negate 2 (sum ac bd))

abbrev pairs := pairsWith mulWords

def addWith (product : ProductKind → Limbs → Limbs → Limbs) (p q : PointWords) : PointWords :=
  let xx := product .xx p.x q.x
  let yy := product .yy p.y q.y
  let zz := product .zz p.z q.z
  let xy := pairsWith (product .xy) p.x p.y q.x q.y xx yy
  let yz := pairsWith (product .yz) p.y p.z q.y q.z yy zz
  let xz := pairsWith (product .xz) p.x p.z q.x q.z xx zz
  let bzz3 := weak (scale 21 zz)
  let minus := sum yy (negate 1 bzz3)
  let plus := sum yy bzz3
  let byz3 := weak (scale 3 (weak (scale 7 yz)))
  let xx3 := scale 3 xx
  let bxx9 := weak (scale 7 (weak (scale 9 xx)))
  ⟨weak (sum (product .xLeft xy minus) (negate 1 (product .xRight byz3 xz))),
    weak (sum (product .yLeft plus minus) (product .yRight bxx9 xz)),
    weak (sum (product .zLeft yz plus) (product .zRight xx3 xy))⟩

def add : PointWords → PointWords → PointWords := addWith (fun _ => mulWords)

end AddWords
end K256.Proofs.Common.Point
