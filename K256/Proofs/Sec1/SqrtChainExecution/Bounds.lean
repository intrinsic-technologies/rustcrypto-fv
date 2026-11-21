import K256.Proofs.Sec1.SqrtChainExecution.Stages

namespace K256.Proofs.Sec1.SqrtChainExecution

open Common.Field

private theorem iter_repr (k : Nat) {a : Limbs} {x : Fin modulus} (h : FieldRepr a x 8) :
    ∃ y, FieldRepr (SqrtChain.iter squareWords k a) y 8 := by
  induction k generalizing a x with
  | zero => exact ⟨x,h⟩
  | succ k ih => exact ih ((squareWords_repr _ _ h).mono (by decide))

private theorem lookup_repr {vs : List Limbs} {a : Limbs} (i : Nat)
    (ha : ∃ x, FieldRepr a x 8) (hv : ∀ w ∈ vs, ∃ x, FieldRepr w x 8) :
    ∃ x, FieldRepr (vs.getD i a) x 8 := by
  by_cases hi : i < vs.length
  · rw [← List.getElem_eq_getD (h := hi)]
    exact hv _ (List.getElem_mem hi)
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : vs.length ≤ i),
      Option.getD_none] using ha

theorem chainWord_repr {a : Limbs} {x : Fin modulus} (ha : FieldRepr a x 8) (i : Nat) :
    ∃ y, FieldRepr (words a i) y 8 := by
  have preserve (ss : List SqrtChain.Step) (vs : List Limbs)
      (hv : ∀ w ∈ vs, ∃ y, FieldRepr w y 8) :
      ∀ w ∈ SqrtChain.runFrom squareWords mulWords a vs ss, ∃ y, FieldRepr w y 8 := by
    induction ss generalizing vs with
    | nil => exact hv
    | cons s ss ih =>
      apply ih
      intro w hw
      rcases List.mem_append.mp hw with old | new
      · exact hv w old
      obtain rfl := List.mem_singleton.mp new
      cases s with
      | sqr j k =>
        obtain ⟨y,hy⟩ := lookup_repr j ⟨x,ha⟩ hv
        exact iter_repr k hy
      | mul j k =>
        obtain ⟨u,hu⟩ := lookup_repr j ⟨x,ha⟩ hv
        obtain ⟨v,hv⟩ := lookup_repr k ⟨x,ha⟩ hv
        exact ⟨u*v,(mulWords_repr _ _ _ _ hu hv).mono (by decide)⟩
  exact lookup_repr i ⟨x,ha⟩ (preserve SqrtChain.chain [a] (fun w h => List.mem_singleton.mp h ▸ ⟨x,ha⟩))

theorem high_product_bound {a : Limbs} {x : Fin modulus} (ha : FieldRepr a x 8) (i j : Nat) :
    (words a i)[4].toNat * (words a j)[4].toNat < 2^116 := by
  have bound (k : Nat) : (words a k)[4].toNat ≤ 16 * (2^48 - 1) := by
    obtain ⟨_,h⟩ := chainWord_repr ha k
    exact h.1 4
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (bound i) (bound j)) (by decide)

end K256.Proofs.Sec1.SqrtChainExecution
