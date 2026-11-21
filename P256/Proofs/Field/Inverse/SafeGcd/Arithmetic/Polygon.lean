import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Model
import Init.GrindInstances.Ring.Rat
import Init.Grind.Ordered.Rat

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Contraction

structure Plane where
  a : Rat
  b : Rat
  c : Rat
  deriving Inhabited, DecidableEq

structure Transform where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  deriving DecidableEq

def Contains (ps : List Plane) (x y t : Rat) : Prop :=
  ∀ p ∈ ps, p.a * x + p.b * y ≤ p.c * t

theorem Contains.scale {ps : List Plane} {x y t k : Rat}
    (h : Contains ps x y t) (hk : 0 ≤ k) : Contains ps (k*x) (k*y) (k*t) := by
  intro p hp
  have hn := Rat.mul_le_mul_of_nonneg_left (h p hp) hk
  grind

theorem Contains.add {ps : List Plane} {x y t u v z : Rat}
    (h : Contains ps x y t) (j : Contains ps u v z) :
    Contains ps (x+u) (y+v) (t+z) := by
  intro p hp
  have hn := h p hp
  have jn := j p hp
  grind

structure Witness where
  i : Nat
  j : Nat
  l : Rat
  m : Rat
  deriving DecidableEq

def Witness.Valid (w : Witness) (ps : List Plane) (r : Plane) (m : Transform) : Prop :=
  w.i < ps.length ∧ w.j < ps.length ∧ 0 ≤ w.l ∧ 0 ≤ w.m ∧
  w.l * ps[w.i]!.a + w.m * ps[w.j]!.a = r.a * m.a + r.b * m.c ∧
  w.l * ps[w.i]!.b + w.m * ps[w.j]!.b = r.a * m.b + r.b * m.d ∧
  w.l * ps[w.i]!.c + w.m * ps[w.j]!.c ≤ r.c

instance (w : Witness) (ps : List Plane) (r : Plane) (m : Transform) :
    Decidable (w.Valid ps r m) := inferInstanceAs (Decidable (_ ∧ _))

theorem Witness.sound {w : Witness} {ps : List Plane} {r : Plane} {m : Transform}
    (valid : w.Valid ps r m) {x y t : Rat} (ht : 0 ≤ t) (h : Contains ps x y t) :
    r.a * (m.a*x+m.b*y) + r.b * (m.c*x+m.d*y) ≤ r.c*t := by
  rcases valid with ⟨hi, hj, hl, hm, hx, hy, hz⟩
  have hp : ps[w.i]! ∈ ps := by simpa only [List.getElem!_eq_getElem?_getD,
    (List.getElem?_eq_getElem hi), Option.getD_some] using List.getElem_mem hi
  have hq : ps[w.j]! ∈ ps := by simpa only [List.getElem!_eq_getElem?_getD,
    (List.getElem?_eq_getElem hj), Option.getD_some] using List.getElem_mem hj
  have h1 := Rat.mul_le_mul_of_nonneg_left (h _ hp) hl
  have h2 := Rat.mul_le_mul_of_nonneg_left (h _ hq) hm
  have h3 := Rat.mul_le_mul_of_nonneg_right hz ht
  calc
    _ = w.l * (ps[w.i]!.a*x+ps[w.i]!.b*y) +
        w.m * (ps[w.j]!.a*x+ps[w.j]!.b*y) := by grind only
    _ ≤ w.l * (ps[w.i]!.c*t) + w.m * (ps[w.j]!.c*t) := by grind only
    _ = (w.l * ps[w.i]!.c + w.m * ps[w.j]!.c)*t := by grind only
    _ ≤ r.c*t := h3

def Certifies (ps : List Plane) (m : Transform) : List Plane → List Witness → Prop
  | [], [] => True
  | p::qs, w::ws => w.Valid ps p m ∧ Certifies ps m qs ws
  | _, _ => False

noncomputable instance (ps : List Plane) (m : Transform) (qs : List Plane) (ws : List Witness) :
    Decidable (Certifies ps m qs ws) := by
  induction qs generalizing ws with
  | nil => cases ws <;> dsimp only [Certifies] <;> infer_instance
  | cons q qs ih =>
    cases ws with
    | nil => exact isFalse id
    | cons w ws =>
      dsimp only [Certifies]
      have : Decidable (Certifies ps m qs ws) := ih ws
      infer_instance

theorem Certifies.sound {ps qs : List Plane} {m : Transform} {ws : List Witness}
    (hcert : Certifies ps m qs ws) {x y t : Rat} (ht : 0 ≤ t) (h : Contains ps x y t) :
    Contains qs (m.a*x+m.b*y) (m.c*x+m.d*y) t := by
  induction qs generalizing ws with
  | nil => intro p hp; contradiction
  | cons q qs ih =>
    cases ws with
    | nil => exact False.elim hcert
    | cons w ws =>
      rcases hcert with ⟨hw, hws⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Witness.sound hw ht h
      · exact ih hws p hp

end P256.Proofs.Field.Inverse.SafeGcd.Contraction
