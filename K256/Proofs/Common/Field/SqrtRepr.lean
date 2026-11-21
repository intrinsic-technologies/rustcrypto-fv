import K256.Proofs.Common.Field.SquareValue
import K256.Proofs.Common.Field.SqrtChain

namespace K256.Proofs.Common.Field

theorem FieldRepr.mono {a : Limbs} {x : Fin modulus} {m n : Nat}
    (h : FieldRepr a x m) (hmn : m ≤ n) : FieldRepr a x n := by
  refine ⟨fun i => ?_, h.2⟩
  have hi := h.1 i
  split <;> rename_i ht <;> simp only [ht, ite_true, ite_false] at hi <;>
    exact Nat.le_trans hi (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hmn))

namespace SqrtChain

theorem result_rel {α β : Type} (R : α → β → Prop)
    (sq : α → α) (mul : α → α → α) (sq' : β → β) (mul' : β → β → β)
    (hsq : ∀ a b, R a b → R (sq a) (sq' b))
    (hmul : ∀ a b c d, R a c → R b d → R (mul a b) (mul' c d))
    {a : α} {b : β} (hab : R a b) (steps : List Step) :
    R (result sq mul a steps) (result sq' mul' b steps) := by
  let A := {p : α × β // R p.1 p.2}
  let s (v : A) : A := ⟨(sq v.val.1, sq' v.val.2), hsq _ _ v.property⟩
  let m (v w : A) : A :=
    ⟨(mul v.val.1 w.val.1, mul' v.val.2 w.val.2), hmul _ _ _ _ v.property w.property⟩
  let v : A := ⟨(a, b), hab⟩
  have left := result_map (fun p : A => p.val.1) s m v sq mul
    (fun _ => rfl) (fun _ _ => rfl) steps
  have right := result_map (fun p : A => p.val.2) s m v sq' mul'
    (fun _ => rfl) (fun _ _ => rfl) steps
  exact left ▸ right ▸ (result s m v steps).property

theorem result_repr (mul : Limbs → Limbs → Limbs)
    (hmul : ∀ a b x y, FieldRepr a x 8 → FieldRepr b y 8 → FieldRepr (mul a b) (x * y) 1)
    {a : Limbs} {x : Fin modulus} (ha : FieldRepr a x 8) :
    FieldRepr (result squareWords mul a chain)
      ⟨x.val ^ ((modulus + 1) / 4) % modulus, Nat.mod_lt _ (by decide)⟩ 8 := by
  let sq (x : Fin modulus) := x * x
  have h := result_rel (fun a x => FieldRepr a x 8) squareWords mul sq (· * ·)
    (fun a x hx => (squareWords_repr a x hx).mono (by decide))
    (fun a b x y hx hy => (hmul a b x y hx hy).mono (by decide)) ha chain
  have hv := result_map Fin.val sq (· * ·) x modSq modMul
    (fun _ => rfl) (fun _ _ => rfl) chain
  have he : result sq (· * ·) x chain =
      ⟨x.val ^ ((modulus + 1) / 4) % modulus, Nat.mod_lt _ (by decide)⟩ :=
    Fin.ext (hv.trans (result_sqrt x))
  exact he ▸ h

end SqrtChain
end K256.Proofs.Common.Field
