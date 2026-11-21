import K256.Proofs.Ecdh.Curve
import K256.Proofs.Verify.Naf.Recoding

namespace K256.Proofs.Verify

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

def wnafAccumulator (bases : Fin 4 → Curve.Point) : Nat → (Fin 4 → List Int) → Curve.Point
  | 0, _ => .infinity
  | n+1, ds =>
    let p := wnafAccumulator bases n (fun i => (ds i).tail)
    let addDigit := fun q i => Curve.add domain q (selectDigit (bases i) ((ds i).headD 0))
    addDigit (addDigit (addDigit (addDigit (Curve.add domain p p) 0) 1) 2) 3

private theorem value_head_tail (ds : List Int) :
    Naf.value ds = ds.headD 0 + 2 * Naf.value ds.tail := by
  cases ds <;> simp [Naf.value, List.headD]

private theorem wnafAccumulator_multiple (a : Fin 4 → Int) (n : Nat) (ds : Fin 4 → List Int)
    (length : ∀ i, (ds i).length ≤ n) :
    wnafAccumulator (fun i => generatorMultiple (a i)) n ds =
      generatorMultiple (Naf.value (ds 0) * a 0 + Naf.value (ds 1) * a 1 +
        Naf.value (ds 2) * a 2 + Naf.value (ds 3) * a 3) := by
  induction n generalizing ds with
  | zero =>
    have nil (i) : ds i = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (length i))
    simp only [wnafAccumulator, nil, Naf.value, List.foldr_nil, Int.zero_mul, Int.add_zero]
    decide +kernel
  | succ n ih =>
    have bound (i) : (ds i).tail.length ≤ n := by
      have := length i
      rw [List.length_tail]
      omega
    rw [wnafAccumulator, ih _ bound]
    simp only [selectDigit_multiple, generatorMultiple_add]
    congr 1
    rw [value_head_tail (ds 0), value_head_tail (ds 1),
      value_head_tail (ds 2), value_head_tail (ds 3)]
    grind only

private theorem signedBase_onCurve (a : Int) (p : Curve.Point) (hp : Curve.onCurve domain p) :
    Curve.onCurve domain (signedBase a p) := by
  obtain ⟨k, rfl⟩ := Ecdh.Curve.exists_generatorMultiple p hp
  unfold signedBase
  split
  · rw [generatorMultiple_neg]
    exact generatorMultiple_onCurve _
  · exact generatorMultiple_onCurve _

private theorem endomorphism_onCurve (p : Curve.Point) (hp : Curve.onCurve domain p) :
    Curve.onCurve domain (endomorphism p) := by
  obtain ⟨k, rfl⟩ := Ecdh.Curve.exists_generatorMultiple p hp
  rw [Ecdh.Curve.endomorphism_generatorMultiple]
  exact generatorMultiple_onCurve _

def combinationBases (p : Curve.Point) (u v : Nat) : Fin 4 → Curve.Point
  | 0 => signedBase (centered (splitFirst u)) domain.G
  | 1 => signedBase (centered (splitSecond u)) (endomorphism domain.G)
  | 2 => signedBase (centered (splitFirst v)) p
  | 3 => signedBase (centered (splitSecond v)) (endomorphism p)

def combinationScalars (u v : Nat) : Fin 4 → Nat
  | 0 => (centered (splitFirst u)).natAbs
  | 1 => (centered (splitSecond u)).natAbs
  | 2 => (centered (splitFirst v)).natAbs
  | 3 => (centered (splitSecond v)).natAbs

theorem wnafAccumulator_correct (p : Curve.Point) (u v count : Nat) (hp : Curve.onCurve domain p)
    (hu : u < domain.n) (hv : v < domain.n)
    (length : ∀ i, (Naf.digits (combinationScalars u v i)).length ≤ count) :
    wnafAccumulator (combinationBases p u v) count (fun i => Naf.digits (combinationScalars u v i)) =
      Curve.add domain (Curve.scalarMul domain u domain.G) (Curve.scalarMul domain v p) := by
  let ds (i : Fin 4) := Naf.digits (combinationScalars u v i)
  have value (i : Fin 4) : Naf.value (ds i) = (combinationScalars u v i : Int) := by
    apply Naf.digits_value
    match i with
    | 0 => exact (split_correct u hu).2.1
    | 1 => exact (split_correct u hu).2.2
    | 2 => exact (split_correct v hv).2.1
    | 3 => exact (split_correct v hv).2.2
  have onCurve (i : Fin 4) : Curve.onCurve domain (combinationBases p u v i) := by
    have hg := Group.generator_onCurve
    match i with
    | 0 => exact signedBase_onCurve (centered (splitFirst u)) domain.G hg
    | 1 => exact signedBase_onCurve _ _ (endomorphism_onCurve _ hg)
    | 2 => exact signedBase_onCurve (centered (splitFirst v)) p hp
    | 3 => exact signedBase_onCurve _ _ (endomorphism_onCurve _ hp)
  let a (i : Fin 4) := Classical.choose (Ecdh.Curve.exists_generatorMultiple _ (onCurve i))
  have base (i : Fin 4) : combinationBases p u v i = generatorMultiple (a i) :=
    Classical.choose_spec (Ecdh.Curve.exists_generatorMultiple _ (onCurve i))
  rw [funext base, wnafAccumulator_multiple a count ds length,
    ← Ecdh.Curve.peerWindow_eq_scalarMul _ Group.generator_onCurve _ hu,
    ← Ecdh.Curve.peerWindow_eq_scalarMul _ hp _ hv]
  let b := combinationBases p u v
  let s := combinationScalars u v
  change _ = Curve.add domain (signedWindow (b 0) (b 1) 32 (s 0) (s 1))
    (signedWindow (b 2) (b 3) 32 (s 2) (s 3))
  rw [show (b 0) = _ from base 0, show (b 1) = _ from base 1,
    show (b 2) = _ from base 2, show (b 3) = _ from base 3,
    signedWindow_multiple, signedWindow_multiple, generatorMultiple_add,
    value 0, value 1, value 2, value 3, Int.add_assoc ((s 0) * a 0 + (s 1) * a 1)]

end K256.Proofs.Verify
