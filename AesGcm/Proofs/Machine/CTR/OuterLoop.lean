import Init

namespace AesGcm.Proofs.Machine.CTR

theorem outer_loop
    {α : Type} (P : Nat → α → Prop)
    (limit : Nat)
    (step : ∀ n a, n < limit → P n a → ∃ b, P (n + 1) b)
    (a : α) (h : P 0 a) : ∃ b, P limit b := by
  have walk : ∀ n ≤ limit, ∃ b, P n b := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨a, h⟩
    | succ n ih =>
      intro bound
      obtain ⟨b, hb⟩ := ih (Nat.le_of_succ_le bound)
      exact step n b bound hb
  exact walk limit (Nat.le_refl _)

end AesGcm.Proofs.Machine.CTR
