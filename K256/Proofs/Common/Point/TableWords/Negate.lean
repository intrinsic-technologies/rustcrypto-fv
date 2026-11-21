import K256.Proofs.Common.Point.DoubleWords.Field
import K256.Proofs.Generate.Generator.Multiply.Coordinates
import K256.Proofs.Sec1.Affine.Compressed.Parity

namespace K256.Proofs.Common.Point.TableWords

open Field AddWords Sec1.Affine.Compressed Sec1.Serialize.Normalize X86.Machine X86Proofs Refine Generate.Generator.Multiply

private abbrev pack (t0 t1 t2 t3 high : Word) : Limbs :=
  #v[t0 &&& mask52, t1 &&& mask52, t2 &&& mask52, t3 &&& mask52, top t3 high]

def negateY (a : Limbs) : Limbs :=
  let high := (0x3fffffffffffc : Word) - a[4]
  let t0 := ((high >>> 48) * 0x1000003d1 - a[0]) + (0x3ffffbfffff0bc : Word)
  let t1 := ((t0 >>> 52) - a[1]) + (0x3ffffffffffffc : Word)
  let t2 := ((t1 >>> 52) - a[2]) + (0x3ffffffffffffc : Word)
  let t3 := ((t2 >>> 52) - a[3]) + (0x3ffffffffffffc : Word)
  pack t0 t1 t2 t3 high

private theorem negWord (a : Limbs) (i : Fin 5) :
    (negate 1 a)[i.val] = negationOffset i - a[i.val] := by
  have coeff : ∀ j : Fin 5, modulusWords[j.val] * 4 = negationOffset j := by decide +kernel
  simp only [negate, Vector.getElem_ofFn]
  change modulusWords[i.val] * 4 - a[i.val] = negationOffset i - a[i.val]
  rw [coeff]

private theorem reorder (u v k : Word) : u - v + k = u + (k - v) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-v) k]

private theorem weakPack (b : Limbs) : weak b =
    let t0 := first b
    let t1 := carry t0 b[1]
    let t2 := carry t1 b[2]
    let t3 := carry t2 b[3]
    pack t0 t1 t2 t3 b[4] := rfl

private theorem negLimbs (a : Limbs) : negateY a = weak (negate 1 a) := by
  have h0 : (negate 1 a)[0] = (0x3ffffbfffff0bc : Word) - a[0] := negWord a 0
  have h1 : (negate 1 a)[1] = (0x3ffffffffffffc : Word) - a[1] := negWord a 1
  have h2 : (negate 1 a)[2] = (0x3ffffffffffffc : Word) - a[2] := negWord a 2
  have h3 : (negate 1 a)[3] = (0x3ffffffffffffc : Word) - a[3] := negWord a 3
  have h4 : (negate 1 a)[4] = (0x3fffffffffffc : Word) - a[4] := negWord a 4
  simp only [negateY, weakPack, first, carry, h0, h1, h2, h3, h4, reorder]

theorem negateY_repr {a : Limbs} {y : Fin modulus} (h : FieldRepr a y 1) :
    FieldRepr (negateY a) (-y) 1 := by
  rw [negLimbs]
  exact weak_repr (negate_repr h (by decide)) (by decide)

theorem storedNeg {p : Projective} {m n : Ram} {src dst : Word} (input : p.Stored m src)
    (copyX : ∀ i : Fin 5,
      memLoad n (wordAddr dst 64 i.val) 64 = memLoad m (wordAddr src 64 i.val) 64)
    (copyZ : ∀ i : Fin 5,
      memLoad n (wordAddr (dst+80) 64 i.val) 64 = memLoad m (wordAddr (src+80) 64 i.val) 64)
    (newY : WordsAt n (dst+40) 64 (negateY (Vector.ofFn fun i : Fin 5 =>
      memLoad m (wordAddr (src+40) 64 i.val) 64))) :
    p.neg.Stored n dst := by
  obtain ⟨x,y,z,wx,wy,wz,hx,hy,hz⟩ := input.coordinates
  have eqy : (Vector.ofFn fun i : Fin 5 => memLoad m (wordAddr (src+40) 64 i.val) 64) = y := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_ofFn] using wy i hi
  rw [eqy] at newY
  exact ⟨x,negateY y,z,fun i hi => (copyX ⟨i,hi⟩).trans (wx i hi), newY,
    fun i hi => (copyZ ⟨i,hi⟩).trans (wz i hi), hx, negateY_repr hy, hz⟩

end K256.Proofs.Common.Point.TableWords
