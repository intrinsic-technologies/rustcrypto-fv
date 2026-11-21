import P256.Proofs.Verifying.Combination.Naf.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf

open Prelude X86 X86.Machine X86Proofs

theorem ValidDigit.bounds {d : Int} (h : ValidDigit d) : -15 ≤ d ∧ d ≤ 15 := by
  rcases h with rfl | ⟨_, lo, hi⟩
  · decide
  · exact ⟨lo, hi⟩

theorem ValidDigit.decode {d : Int} (h : ValidDigit d) :
    (BitVec.ofInt 8 d).toInt = d := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · have := h.bounds; omega
  · have := h.bounds; omega

theorem getD_valid {ds : List Int} (h : ∀ d ∈ ds, ValidDigit d) (i : Nat) :
    ValidDigit ((ds[i]?).getD 0) := by
  cases he : ds[i]? with
  | none => exact Or.inl rfl
  | some d =>
    obtain ⟨hi, hd⟩ := List.getElem?_eq_some_iff.mp he
    exact hd ▸ h _ (List.getElem_mem hi)

theorem digits_getD_valid {n : Nat} (hn : n < 2^256) (i : Nat) :
    ValidDigit (((digits n)[i]?).getD 0) :=
  getD_valid (digits_valid n hn) i

theorem DigitsAt.signed {s : RamState} {address : BitVec 64} {ds : List Int}
    (hmem : DigitsAt s address ds) (valid : ∀ d ∈ ds, ValidDigit d) {i : Nat}
    (hi : i < 257) :
    (memLoad s.external (address + BitVec.ofNat 64 i) 8).toInt = (ds[i]?).getD 0 := by
  rw [hmem i hi]
  exact (getD_valid valid i).decode

theorem DigitsAt.zero_tail {s : RamState} {address : BitVec 64} {ds : List Int}
    (hmem : DigitsAt s address ds) {i : Nat} (hi : i < 257) (tail : ds.length ≤ i) :
    memLoad s.external (address + BitVec.ofNat 64 i) 8 = 0 := by
  rw [hmem i hi, List.getElem?_eq_none (by omega)]
  rfl

theorem DigitsAt.of_copy {s t : RamState} {source destination : BitVec 64} {ds : List Int}
    (hmem : DigitsAt s source ds)
    (bytes : ∀ i < 257, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : DigitsAt t destination ds := by
  intro i hi
  rw [← hmem i hi]
  apply memLoad_congr
  intro j hj
  have hz : j = 0 := by omega
  subst j
  simp only [BitVec.add_zero]
  change (t.external[destination + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[source + BitVec.ofNat 64 i]?).getD 0
  rw [bytes i hi]

theorem value_append_zeroes (ds : List Int) (k : Nat) :
    value (ds ++ List.replicate k 0) = value ds := by
  induction ds with
  | nil =>
    simpa only [List.nil_append, List.append_nil, value, List.foldr_nil, Int.mul_zero] using
      value_zeroes k []
  | cons d ds ih => rw [List.cons_append, value_cons, ih, value_cons]

theorem NafAt.of_copy {s t : RamState} {source destination : BitVec 64} {n : Nat}
    (h : NafAt s source n)
    (bytes : ∀ i < 272, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : NafAt t destination n := by
  constructor
  · rw [← h.length]
    apply memLoad_congr
    intro i hi
    change (t.external[destination + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[source + BitVec.ofNat 64 i]?).getD 0
    rw [bytes i (by omega)]
  · intro i hi
    rw [← h.digit i hi]
    apply memLoad_congr
    intro j hj
    have hj' : j = 0 := by omega
    subst j
    simp only [BitVec.add_zero]
    change (t.external[destination + 8 + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[source + 8 + BitVec.ofNat 64 i]?).getD 0
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    have hh := bytes (8+i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc] at hh
    exact hh

end P256.Proofs.Verifying.Combination.Naf
