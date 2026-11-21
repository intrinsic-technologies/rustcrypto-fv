import K256.Proofs.Ecdh.Curve.Counting
import K256.Proofs.Generate.Curve

namespace K256.Proofs.Ecdh.Curve
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve Group
open CurveArithmetic Fin.NatCast

private abbrev ValidPoint := {p : Curve.Point // Curve.onCurve domain p = true}

private instance : Add ValidPoint :=
  ⟨fun p q => ⟨Curve.add domain p.val q.val, secp256k1_add_closed _ _ p.property q.property⟩⟩

private instance : Zero ValidPoint := ⟨⟨.infinity, rfl⟩⟩

private def gen (i : Int) : ValidPoint := ⟨generatorMultiple i, generatorMultiple_onCurve i⟩

private theorem gen_add (i j : Int) : gen i + gen j = gen (i + j) :=
  Subtype.ext (generatorMultiple_add i j)

private theorem gen_zero : gen 0 = 0 := Subtype.ext (by decide +kernel)

private theorem add_zero_pt (p : ValidPoint) : p + 0 = p := by
  apply Subtype.ext
  change Curve.add domain p.val .infinity = p.val
  cases p.val <;> rfl

private instance : Std.Associative (α := ValidPoint) (· + ·) :=
  ⟨fun p q r => Subtype.ext (secp256k1_add_laws.assoc _ _ _ p.property q.property r.property)⟩

private theorem encode_inj {p q : ValidPoint} (h : encodePoint p.val = encodePoint q.val) : p = q :=
  Subtype.ext ((decode_encode _ p.property).symm.trans ((congrArg decodePoint h).trans
    (decode_encode _ q.property)))

private instance : Std.Commutative (α := ValidPoint) (· + ·) := by
  constructor
  intro p q
  apply encode_inj
  change encodePoint (Curve.add domain p.val q.val) = encodePoint (Curve.add domain q.val p.val)
  rw [encode_add _ _ p.property q.property, encode_add _ _ q.property p.property]
  exact Affine.add_comm _ _ _ _ (encode_onCurve _ p.property) (encode_onCurve _ q.property)

private theorem cancel_pt {p q r : ValidPoint} (h : p + q = p + r) : q = r := by
  apply encode_inj
  apply Affine.add_left_cancel _ _ secp256k1_two_ne_zero secp256k1_cubic_ne_zero
    (encodePoint p.val) _ _ (encode_onCurve _ p.property) (encode_onCurve _ q.property)
    (encode_onCurve _ r.property)
  rw [← encode_add _ _ p.property q.property, ← encode_add _ _ p.property r.property]
  exact congrArg (fun x : ValidPoint => encodePoint x.val) h

private theorem eq_zero_of_double {p : ValidPoint} (h : p + p = 0) : p = 0 := by
  apply encode_inj
  have he := congrArg (fun x : ValidPoint => encodePoint x.val) h
  change encodePoint (Curve.add domain p.val p.val) = Affine.Point.infinity at he
  rw [encode_add _ _ p.property p.property] at he
  have hn := (Affine.add_eq_infinity_iff _ _ _).mp he
  have hp := encode_onCurve _ p.property
  cases heq : encodePoint p.val with
  | infinity => rfl
  | affine x y =>
    rw [heq] at hn hp
    have hy : y = -y := (Affine.Point.affine.inj hn).2
    exact False.elim ((Affine.affine_double_den _ _ x y secp256k1_two_ne_zero
      secp256k1_cubic_ne_zero hp) (by grind only))

private theorem translate_eq_gen {p : ValidPoint} {i j : Int} (h : p + gen i = gen j) :
    p = gen (j + -i) := by
  calc
    p = p + gen (i + -i) := by rw [show i + -i = 0 by omega, gen_zero, add_zero_pt]
    _ = (p + gen i) + gen (-i) := by rw [← gen_add]; ac_rfl
    _ = gen (j + -i) := by rw [h, gen_add]

private theorem gen_half (k : Int) : ∃ t, gen (t + t) = gen k := by
  let n : Int := domain.n
  have hn : n % 2 = 1 := by decide +kernel
  by_cases he : k % 2 = 0
  · exact ⟨k / 2, congrArg gen (by omega)⟩
  · refine ⟨(k + n) / 2, ?_⟩
    rw [show (k + n) / 2 + (k + n) / 2 = k + n by omega]
    apply Subtype.ext
    change Curve.scalarMul domain ((k + n) % n).toNat domain.G =
      Curve.scalarMul domain (k % n).toNat domain.G
    rw [Int.add_emod_right]

private theorem generator_of_double {p : ValidPoint} {k : Int} (h : p + p = gen k) :
    ∃ a, p = gen a := by
  obtain ⟨t, ht⟩ := gen_half k
  have hz : (p + gen (-t)) + (p + gen (-t)) = 0 := by
    calc
      _ = (p + p) + (gen (-t) + gen (-t)) := by ac_rfl
      _ = gen (t + t + (-t + -t)) := by rw [h, ← ht, gen_add, gen_add]
      _ = 0 := by rw [show t + t + (-t + -t) = 0 by omega, gen_zero]
  exact ⟨_, translate_eq_gen ((eq_zero_of_double hz).trans gen_zero.symm)⟩

private theorem gen_ne_of_lt {i j : Nat} (hij : i < j) (hj : j < domain.n) :
    gen i ≠ gen j := by
  intro he
  have h := congrArg (fun p : ValidPoint => p + gen (-(i : Int))) he
  have hz : gen ((j - i : Nat) : Int) = 0 := by
    rw [Int.natCast_sub (Nat.le_of_lt hij)]
    simpa only [gen_add, show (i : Int) + -i = 0 by omega, gen_zero, Int.sub_eq_add_neg]
      using h.symm
  have hlt : j - i < domain.n := by omega
  apply generatorWindow_ne_infinity (j - i) (by omega) hlt
  rw [generatorWindow_eq_scalarMul _ hlt]
  have hv := congrArg Subtype.val hz
  change Curve.scalarMul domain (((j - i : Nat) : Int) % (domain.n : Int)).toNat domain.G =
    .infinity at hv
  simpa only [Int.ofNat_mod_ofNat, Int.toNat_natCast, Nat.mod_eq_of_lt hlt] using hv

private theorem gen_inj_lt {i j : Nat} (hi : i < domain.n) (hj : j < domain.n)
    (h : gen i = gen j) : i = j := by
  have h₁ := fun hlt : i < j => gen_ne_of_lt hlt hj h
  have h₂ := fun hlt : j < i => gen_ne_of_lt hlt hi h.symm
  exact Nat.le_antisymm (Nat.le_of_not_gt h₂) (Nat.le_of_not_gt h₁)

private def cosetPoint (p : ValidPoint) (row col : Nat) : ValidPoint :=
  match row with
  | 0 => gen col
  | 1 => p + gen col
  | _ => p + (p + gen col)

private theorem cosetPoint_inj (p : ValidPoint) (outside : ¬ ∃ k, p = gen k)
    {r s i j : Nat} (hr : r < 3) (hs : s < 3) (hi : i < domain.n) (hj : j < domain.n)
    (he : cosetPoint p r i = cosetPoint p s j) : r = s ∧ i = j := by
  have adjacent {a b : Nat} (h : p + gen (a : Int) = gen (b : Int)) : False :=
    outside ⟨_, translate_eq_gen h⟩
  have distant {a b : Nat} (h : p + (p + gen (a : Int)) = gen (b : Int)) : False := by
    have hh : (p + p) + gen (a : Int) = gen (b : Int) := by
      calc
        _ = p + (p + gen (a : Int)) := by ac_rfl
        _ = _ := h
    exact outside (generator_of_double (translate_eq_gen hh))
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hr' with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
  · exact ⟨rfl, gen_inj_lt hi hj he⟩
  · exact (adjacent he.symm).elim
  · exact (distant he.symm).elim
  · exact (adjacent he).elim
  · exact ⟨rfl, gen_inj_lt hi hj (cancel_pt he)⟩
  · exact (adjacent (cancel_pt he.symm)).elim
  · exact (distant he).elim
  · exact (adjacent (cancel_pt he)).elim
  · exact ⟨rfl, gen_inj_lt hi hj (cancel_pt (cancel_pt he))⟩

theorem exists_generatorMultiple (p : Curve.Point) (hp : Curve.onCurve domain p = true) :
    ∃ a : Int, p = generatorMultiple a := by
  apply Classical.byContradiction
  intro outside
  let q : ValidPoint := ⟨p, hp⟩
  have hout : ¬ ∃ k, q = gen k := fun ⟨k, h⟩ => outside ⟨k, congrArg Subtype.val h⟩
  let f (i : Fin (3 * domain.n)) := cosetPoint q (i.val % 3) (i.val / 3)
  obtain ⟨i, j, hne, h⟩ := point_collision (fun i => (f i).val) (fun i => (f i).property)
  obtain ⟨hr, hc⟩ := cosetPoint_inj q hout (Nat.mod_lt i.val (by decide : 0 < 3))
    (Nat.mod_lt j.val (by decide : 0 < 3)) (show i.val / 3 < domain.n by omega)
    (show j.val / 3 < domain.n by omega) (Subtype.ext h)
  exact hne (Fin.ext (by omega))

end K256.Proofs.Ecdh.Curve
