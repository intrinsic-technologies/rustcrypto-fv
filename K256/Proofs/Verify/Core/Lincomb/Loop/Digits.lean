import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem preparedDigit {m : Ram} {table header : BitVec 64} {p : Curve.Point} {s : Nat}
    (prepared : Prepared m table header p s) (hs : s < domain.n) (hp : Curve.onCurve domain p)
    (j : Fin 2) (k : Fin 257) :
    let part := centered (if j.val = 1 then splitSecond s else splitFirst s)
    let base := signedBase part (if j.val = 1 then endomorphism p else p)
    let d := (Naf.digits part.natAbs)[k.val]?.getD 0
    memLoad m (header + BitVec.ofNat 64 (0x110 * j.val) + 8 + BitVec.ofNat 64 k.val) 8 =
      BitVec.ofInt 8 d ∧ Naf.ValidDigit d ∧ (d ≠ 0 →
      ∃ q : Projective, q.valid ∧
        q.Stored m (table + BitVec.ofNat 64 (120 * (8 * j.val + d.natAbs / 2))) ∧
        (if d < 0 then q.neg else q).value = selectDigit base d) := by
  intro part base d
  obtain ⟨_, bytes, entries⟩ := prepared j
  have small : part.natAbs < 2^128 := by
    unfold part
    split
    · exact (split_correct s hs).2.2
    · exact (split_correct s hs).2.1
  have valid : Naf.ValidDigit d := by
    unfold d
    cases eqn : (Naf.digits part.natAbs)[k.val]? with
    | none => exact Or.inl rfl
    | some digit =>
      exact Naf.digits_valid _ small _ (List.mem_of_getElem? eqn)
  refine ⟨bytes k, valid, ?_⟩
  intro nz
  have onCurve : Curve.onCurve domain base := by
    obtain ⟨a, rfl⟩ := Ecdh.Curve.exists_generatorMultiple p hp
    simp only [base, signedBase]
    split <;> split <;> simp only [Ecdh.Curve.endomorphism_generatorMultiple,
      generatorMultiple_neg, generatorMultiple_onCurve]
  obtain ⟨fits, value⟩ := Naf.lookup_oddTableEntry base onCurve valid nz
  obtain ⟨q, hv, hval, stored⟩ := entries ⟨_, fits⟩
  refine ⟨q,hv,stored,?_⟩
  split <;> rename_i sign
  · rw [Projective.neg_value, hval]
    exact (ite_eq_left sign).symm.trans value
  · rw [hval]
    exact (ite_eq_right sign).symm.trans value

end K256.Proofs.Verify.Core.Lincomb.Loop
