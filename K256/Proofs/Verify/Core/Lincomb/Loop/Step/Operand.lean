import K256.Proofs.Verify.Core.Lincomb.Loop.Column
import K256.Proofs.Verify.Core.Lincomb.Loop.Digits
import K256.Proofs.Verify.Core.Lincomb.Loop.Packed
import K256.Proofs.Verify.Core.Lincomb.Copy

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Curve
open Generate.Generator.Multiply (Projective)

abbrev digitBase (table : BitVec 64) (j : Fin 4) :=
  row table j + BitVec.ofNat 64 (960*(j.val%2))

abbrev digitAddress (table : BitVec 64) (j : Fin 4) (k : Nat) :=
  row table j + 0x780 + BitVec.ofNat 64 (272*(j.val%2)) + 8 + BitVec.ofNat 64 k

private def RowOperand (m : Ram) (table : BitVec 64) (j : Fin 4) (k scalar : Nat) (base : Curve.Point) : Prop :=
    let d := ((Naf.digits (scalar))[k]?).getD 0
    memLoad m (digitAddress table j k) 8 = BitVec.ofInt 8 d ∧ Naf.ValidDigit d ∧
      (d ≠ 0 → ∃ q : Projective, q.valid ∧
        q.Stored m (digitBase table j + BitVec.ofNat 64 (120*(d.natAbs/2))) ∧
        (if d < 0 then q.neg else q).value = selectDigit (base) d)

private theorem preparedRow {n : Ram} {j : Fin 4} {k scalar : Nat} {base : Curve.Point} {table : BitVec 64} (bound : k < 129) (t hdr : BitVec 64) (s : Nat) (b : Curve.Point) (prep : Prepared n t hdr b s)
      (hs : s < domain.n) (hb : Curve.onCurve domain b) (i : Fin 2)
      (eqS : (centered (if i.val = 1 then splitSecond s else splitFirst s)).natAbs = scalar)
      (eqB : signedBase (centered (if i.val = 1 then splitSecond s else splitFirst s))
        (if i.val = 1 then endomorphism b else b) = base)
      (addr : hdr + BitVec.ofNat 64 (272*i.val) + 8 + BitVec.ofNat 64 k = digitAddress table j k)
      (slot : ∀ z : Nat, t + BitVec.ofNat 64 (120*(8*i.val+z)) =
        digitBase table j + BitVec.ofNat 64 (120*z)) :
    RowOperand n table j k scalar base := by
    have data := preparedDigit prep hs hb i (⟨k, by omega⟩ : Fin 257)
    dsimp only [RowOperand] at data ⊢
    rw [eqS, eqB, addr] at data
    simp only [slot] at data
    exact data

theorem columnOperand {m n : Ram} {sp dst table : BitVec 64}
    {p : Curve.Point} {u v k : Nat} (j : Fin 4)
    (hu : u < domain.n) (hv : v < domain.n) (hp : Curve.onCurve domain p)
    (apart : Outside [scratch sp 0x478, ⟨dst.toNat,120⟩] table 0x1340)
    (frame : RamWriteFrame m n [scratch sp 0x478])
    (generator : Prepared m table (table + 0x780) domain.G u)
    (peer : Prepared m (table + 0x9a0) (table + 0x1120) p v) (bound : k < 129) :
    let d := ((Naf.digits (combinationScalars u v j))[k]?).getD 0
    memLoad n (digitAddress table j k) 8 = BitVec.ofInt 8 d ∧ Naf.ValidDigit d ∧
      (d ≠ 0 → ∃ q : Projective, q.valid ∧
        q.Stored n (digitBase table j + BitVec.ofNat 64 (120*(d.natAbs/2))) ∧
        (if d < 0 then q.neg else q).value = selectDigit (combinationBases p u v j) d) := by
  have copy := Copied.of_frame frame (show Outside [scratch sp 0x478] table 0x1340 from
    ⟨apart.1, fun r hr => apart.2 r (by
      obtain rfl := List.mem_singleton.mp hr
      exact List.Mem.head _)⟩)
  have t0 : Copied m table n table 1920 := fun off w h fit => copy off w h (by omega)
  have g := generator.of_copy t0 (copy.sub (off := 0x780) (by decide))
  have h := peer.of_copy (copy.sub (off := 0x9a0) (by decide)) (copy.sub (off := 0x1120) (by decide))
  change RowOperand n table j k (combinationScalars u v j) (combinationBases p u v j)
  have splitj := (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) j
  rcases splitj with rfl|rfl|rfl|rfl
  · apply preparedRow bound _ _ _ _ g hu Group.generator_onCurve 0
    · simp only [combinationScalars.eq_1,show ((0 : Fin 2).val = 1) = False by decide,↓reduceIte]
    · simp only [combinationBases.eq_1,show ((0 : Fin 2).val = 1) = False by decide,↓reduceIte]
    · change (table + 1920) + 0 + 8 + BitVec.ofNat 64 k =
        table + 1920 + 0 + 8 + BitVec.ofNat 64 k
      bv_omega
    · intro z
      change table + BitVec.ofNat 64 (120*(0+z)) = table + 0 + BitVec.ofNat 64 (120*z)
      rw [Nat.mul_add,BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
  · apply preparedRow bound _ _ _ _ g hu Group.generator_onCurve 1
    · simp only [combinationScalars.eq_2,show ((1 : Fin 2).val = 1) = True by decide,↓reduceIte]
    · simp only [combinationBases.eq_2,show ((1 : Fin 2).val = 1) = True by decide,↓reduceIte]
    · change (table + 1920) + 272 + 8 + BitVec.ofNat 64 k =
        table + 1920 + 272 + 8 + BitVec.ofNat 64 k
      bv_omega
    · intro z
      change table + BitVec.ofNat 64 (120*(8+z)) = table + 960 + BitVec.ofNat 64 (120*z)
      rw [Nat.mul_add,BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
  · apply preparedRow bound _ _ _ _ h hv hp 0
    · simp only [combinationScalars.eq_3,show ((0 : Fin 2).val = 1) = False by decide,↓reduceIte]
    · simp only [combinationBases.eq_3,show ((0 : Fin 2).val = 1) = False by decide,↓reduceIte]
    · change (table + 4384) + 0 + 8 + BitVec.ofNat 64 k =
        (table + 2464) + 1920 + 0 + 8 + BitVec.ofNat 64 k
      bv_omega
    · intro z
      change (table + 2464) + BitVec.ofNat 64 (120*(0+z)) = (table + 2464) + 0 + BitVec.ofNat 64 (120*z)
      rw [Nat.mul_add,BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
  · apply preparedRow bound _ _ _ _ h hv hp 1
    · simp only [combinationScalars.eq_4,show ((1 : Fin 2).val = 1) = True by decide,↓reduceIte]
    · simp only [combinationBases.eq_4,show ((1 : Fin 2).val = 1) = True by decide,↓reduceIte]
    · change (table + 4384) + 272 + 8 + BitVec.ofNat 64 k =
        (table + 2464) + 1920 + 272 + 8 + BitVec.ofNat 64 k
      bv_omega
    · intro z
      change (table + 2464) + BitVec.ofNat 64 (120*(8+z)) = (table + 2464) + 960 + BitVec.ofNat 64 (120*z)
      rw [Nat.mul_add,BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl

end K256.Proofs.Verify.Core.Lincomb.Loop
