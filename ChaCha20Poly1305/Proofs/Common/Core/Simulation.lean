namespace ChaCha20Poly1305.Proofs

structure Semantics where

  State : Type

  Output : Type

  Step : State → State → Prop

  Ret : State → Output → Prop

inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star r a a
  | step {a b c : α} : r a b → Star r b c → Star r a c

namespace Semantics

abbrev Reaches (L : Semantics) : L.State → L.State → Prop := Star L.Step

inductive Exec (L : Semantics) : L.State → L.Output → Prop where
  | ret {s : L.State} {o : L.Output} : L.Ret s o → Exec L s o
  | step {s t : L.State} {o : L.Output} : L.Step s t → Exec L t o → Exec L s o

variable {L : Semantics} {s t u : L.State} {o : L.Output}

theorem Reaches.single (h : L.Step s t) : L.Reaches s t := .step h (.refl t)

theorem Reaches.trans (h₁ : L.Reaches s t) (h₂ : L.Reaches t u) : L.Reaches s u := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem Reaches.tail (h : L.Reaches s t) (hs : L.Step t u) : L.Reaches s u :=
  h.trans (.single hs)

theorem Reaches.exec (h : L.Reaches s t) (he : L.Exec t o) : L.Exec s o := by
  induction h with
  | refl => exact he
  | step hs _ ih => exact .step hs (ih he)

theorem exec_iff : L.Exec s o ↔ ∃ t, L.Reaches s t ∧ L.Ret t o := by
  constructor
  · intro h
    induction h with
    | ret hr => exact ⟨_, .refl _, hr⟩
    | step hs _ ih =>
      obtain ⟨t, hr, hret⟩ := ih
      exact ⟨t, .step hs hr, hret⟩
  · rintro ⟨t, hr, hret⟩
    exact hr.exec (.ret hret)

abbrev segment (L : Semantics) : Semantics where
  State := L.State
  Output := L.State
  Step := L.Step
  Ret := Eq

theorem segment_exec_iff {s t : L.State} : L.segment.Exec s t ↔ L.Reaches s t := by
  rw [exec_iff (L := L.segment)]
  constructor
  · rintro ⟨u, hr, rfl⟩
    exact hr
  · intro h
    exact ⟨t, h, rfl⟩

end Semantics

structure Simulation (lo hi : Semantics) (R : hi.State → lo.State → Prop)
    (post : hi.Output → lo.Output → Prop) : Prop where

  step : ∀ {x y : hi.State} {a : lo.State}, R x a → hi.Step x y → ∃ b, lo.Reaches a b ∧ R y b

  ret : ∀ {x : hi.State} {o : hi.Output} {a : lo.State}, R x a → hi.Ret x o →
    ∃ o', lo.Exec a o' ∧ post o o'

namespace Simulation

variable {lo mid hi : Semantics} {R : hi.State → lo.State → Prop}
  {post : hi.Output → lo.Output → Prop}

theorem reaches (sim : Simulation lo hi R post) {x y : hi.State} (h : hi.Reaches x y)
    {a : lo.State} (ha : R x a) : ∃ b, lo.Reaches a b ∧ R y b := by
  induction h generalizing a with
  | refl => exact ⟨a, .refl a, ha⟩
  | step hs _ ih =>
    obtain ⟨b, hab, hb⟩ := sim.step ha hs
    obtain ⟨c, hbc, hc⟩ := ih hb
    exact ⟨c, hab.trans hbc, hc⟩

theorem exec (sim : Simulation lo hi R post) {x : hi.State} {o : hi.Output} (h : hi.Exec x o)
    {a : lo.State} (ha : R x a) : ∃ o', lo.Exec a o' ∧ post o o' := by
  induction h generalizing a with
  | ret hr => exact sim.ret ha hr
  | step hs _ ih =>
    obtain ⟨b, hab, hb⟩ := sim.step ha hs
    obtain ⟨o', he, hpost⟩ := ih hb
    exact ⟨o', hab.exec he, hpost⟩

theorem refl (L : Semantics) : Simulation L L Eq Eq where
  step := by
    rintro x y a rfl hs
    exact ⟨y, .single hs, rfl⟩
  ret := by
    rintro x o a rfl hr
    exact ⟨o, .ret hr, rfl⟩

theorem trans {R₁ : mid.State → lo.State → Prop} {post₁ : mid.Output → lo.Output → Prop}
    {R₂ : hi.State → mid.State → Prop} {post₂ : hi.Output → mid.Output → Prop}
    (sim₁ : Simulation lo mid R₁ post₁) (sim₂ : Simulation mid hi R₂ post₂) :
    Simulation lo hi (fun x a => ∃ m, R₂ x m ∧ R₁ m a)
      (fun o o'' => ∃ o', post₂ o o' ∧ post₁ o' o'') where
  step := by
    rintro x y a ⟨m, hm, ha⟩ hs
    obtain ⟨m', hmm, hm'⟩ := sim₂.step hm hs
    obtain ⟨b, hab, hb⟩ := sim₁.reaches hmm ha
    exact ⟨b, hab, m', hm', hb⟩
  ret := by
    rintro x o a ⟨m, hm, ha⟩ hr
    obtain ⟨o', he, hpost₂⟩ := sim₂.ret hm hr
    obtain ⟨o'', he', hpost₁⟩ := sim₁.exec he ha
    exact ⟨o'', he', o', hpost₂, hpost₁⟩

theorem mono {post' : hi.Output → lo.Output → Prop} (sim : Simulation lo hi R post)
    (hpost : ∀ o o', post o o' → post' o o') : Simulation lo hi R post' where
  step := sim.step
  ret := fun ha hr =>
    let ⟨o', he, hp⟩ := sim.ret ha hr
    ⟨o', he, hpost _ _ hp⟩

end Simulation

end ChaCha20Poly1305.Proofs
