import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Generate.Curve

def suffix (bases : Fin 4 → Curve.Point) (ds : Fin 4 → List Int) (k : Nat) : Curve.Point :=
  wnafAccumulator bases (129 - k) (fun i => (ds i).drop k)

def addColumn (bases : Fin 4 → Curve.Point) (ds : Fin 4 → List Int) (k : Nat)
    (q : Curve.Point) : Curve.Point :=
  let add := fun p i => Curve.add domain p (selectDigit (bases i) ((ds i)[k]?.getD 0))
  add (add (add (add (Curve.add domain q q) 0) 1) 2) 3

theorem suffix_succ {bases : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (hk : k < 129) : suffix bases ds k = addColumn bases ds k (suffix bases ds (k+1)) := by
  unfold suffix addColumn
  rw [show 129 - k = 129 - (k+1) + 1 by omega, wnafAccumulator]
  simp only [List.tail_drop, List.headD_eq_head?_getD, List.head?_drop]

private theorem empty_accumulator (b : Fin 4 → Curve.Point) (k : Nat) :
    wnafAccumulator b k (fun _ => []) = .infinity := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Curve.add domain (Curve.add domain (Curve.add domain (Curve.add domain
      (Curve.add domain (wnafAccumulator b k (fun _ => [])) (wnafAccumulator b k (fun _ => [])))
      .infinity) .infinity) .infinity) .infinity = _
    rw [ih]
    rfl

theorem suffix_initial {b : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (length : ∀ i, (ds i).length ≤ k) : suffix b ds k = .infinity := by
  unfold suffix
  rw [show (fun i => (ds i).drop k) = (fun _ => []) by
    funext i
    exact List.drop_eq_nil_of_le (length i)]
  apply empty_accumulator

theorem suffix_zero (b : Fin 4 → Curve.Point) (ds : Fin 4 → List Int) :
    suffix b ds 0 = wnafAccumulator b 129 ds := by rfl

end K256.Proofs.Verify.Core.Lincomb.Loop
