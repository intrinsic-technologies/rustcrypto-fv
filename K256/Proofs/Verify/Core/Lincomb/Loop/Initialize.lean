import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize.Measure
import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize.Seed

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Curve

private theorem digits_pos (x : Nat) : 0 < (Naf.digits x).length := by
  unfold Naf.digits
  rw [Naf.recode]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  split <;> exact Nat.zero_lt_succ _

private theorem preparedLength {m : Ram} {table ptr offset address : BitVec 64}
    {p : Curve.Point} {x scalar : Nat} (prep : Prepared m table (ptr + offset) p scalar)
    (j : Fin 2) (part : (centered (if j.val = 1 then splitSecond scalar else splitFirst scalar)).natAbs = x)
    (atHeader : ptr + offset + BitVec.ofNat 64 (0x110 * j.val) = address)
    (bound : (Naf.digits x).length ≤ 129) :
    (memLoad m address 64).toNat = (Naf.digits x).length := by
  have value := (prep j).1
  rw [atHeader, part] at value
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem maximumRounds (len : Fin 4 → Nat) (pos : 0 < len 0) (bound : ∀ i, len i ≤ 129) :
    ∃ k, k < 129 ∧ max (max (max (len 0) (len 1)) (len 2)) (len 3) = k+1 ∧
      ∀ i, len i ≤ k+1 := by
  let top := max (max (max (len 0) (len 1)) (len 2)) (len 3)
  have upper : top ≤ 129 :=
    Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨bound 0, bound 1⟩, bound 2⟩, bound 3⟩
  have le (i : Fin 4) : len i ≤ top := by
    dsimp only [top]
    match i with
    | 0 | 1 | 2 | 3 => omega
  have eq : top = top - 1 + 1 := by have := le 0; omega
  exact ⟨top-1, by omega, eq, fun i => Nat.le_trans (le i) (Nat.le_of_eq eq)⟩

private theorem headerBound {m : Ram} {ptr : BitVec 64} {p : Curve.Point} {u v : Nat}
    (hu : u < domain.n) (hv : v < domain.n)
    (g : Prepared m ptr (ptr + 0x780) domain.G u)
    (q : Prepared m (ptr + 0x9a0) (ptr + 0x1120) p v) :
    ∃ k, k < 129 ∧ headerMaximum m ptr = k+1 ∧
      ∀ i, (Naf.digits (combinationScalars u v i)).length ≤ k+1 := by
  let len (i : Fin 4) := (Naf.digits (combinationScalars u v i)).length
  have bound (i : Fin 4) : len i ≤ 129 := by
    apply Naf.digits_length
    match i with
    | 0 => exact (split_correct u hu).2.1
    | 1 => exact (split_correct u hu).2.2
    | 2 => exact (split_correct v hv).2.1
    | 3 => exact (split_correct v hv).2.2
  have h0 := preparedLength (address := ptr + 0x780) (x := combinationScalars u v 0)
    g 0 (by rw [ite_eq_right (by decide)]; exact (combinationScalars.eq_1 u v).symm)
    (by rw [BitVec.add_assoc]; rfl) (bound 0)
  have h1 := preparedLength (address := ptr + 0x890) (x := combinationScalars u v 1)
    g 1 (by rw [ite_eq_left (by decide)]; exact (combinationScalars.eq_2 u v).symm)
    (by rw [BitVec.add_assoc]; rfl) (bound 1)
  have h2 := preparedLength (address := ptr + 0x1120) (x := combinationScalars u v 2)
    q 0 (by rw [ite_eq_right (by decide)]; exact (combinationScalars.eq_3 u v).symm)
    (by rw [BitVec.add_assoc]; rfl) (bound 2)
  have h3 := preparedLength (address := ptr + 0x1230) (x := combinationScalars u v 3)
    q 1 (by rw [ite_eq_left (by decide)]; exact (combinationScalars.eq_4 u v).symm)
    (by rw [BitVec.add_assoc]; rfl) (bound 3)
  unfold headerMaximum
  rw [h0, h1, h2, h3]
  exact maximumRounds len (digits_pos (combinationScalars u v 0)) bound

set_option linter.unusedVariables false in
theorem startRounds {a : Registers} {m : Ram} {sp dst iterator dataPtr : BitVec 64}
    {p : Curve.Point} {u v : Nat} (entry : RoutineEntry a m sp 0x478)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = iterator)
    (hu : u < domain.n) (hv : v < domain.n) (hp : Curve.onCurve domain p)
    (first : memLoad m iterator 64 = dataPtr)
    (last : memLoad m (iterator + 8) 64 = dataPtr + 0x1340)
    (unset : memLoad m (iterator + 16) 64 = 0 ∧ memLoad m (iterator + 64) 64 = 0)
    (nonzero : dataPtr ≠ 0)
    (iterRead : Readable m iterator 112) (tableRead : Readable m dataPtr 0x1340)
    (iterApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] iterator 112)
    (dataApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] dataPtr 0x1340)
    (generator : Prepared m dataPtr (dataPtr + 0x780) domain.G u)
    (peer : Prepared m (dataPtr + 0x9a0) (dataPtr + 0x1120) p v) :
    ∃ k b n, k < 129 ∧ Reaches .l1100a0 a m .l110278 b n ∧
      RoundState a m sp dst dataPtr (combinationBases p u v)
        (fun i => Naf.digits (combinationScalars u v i)) (k+1) b n := by
  obtain ⟨k, bound, maximum, covers⟩ := headerBound hu hv generator peer
  obtain ⟨b, n, route, saved, count, front, nextTable, endPtr, iter, back⟩ :=
    measureFresh entry di si first last unset nonzero iterRead tableRead iterApart dataApart
  obtain ⟨c, t, seed, state⟩ := seedRounds entry saved (count.trans maximum) front nextTable
    endPtr iter back iterRead (suffix_initial (b := combinationBases p u v) covers)
  exact ⟨k, c, t, bound, route.trans seed, state⟩

end K256.Proofs.Verify.Core.Lincomb.Loop
