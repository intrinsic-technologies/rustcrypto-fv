import P256.Proofs.Common.Refine.Lemma.Layout

namespace P256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift Prelude

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}

theorem Layout.simulation (L : Layout P D lifted Ctx) (code : CodeMap) (c₀ : Ctx)
    (h : ∀ label, L.BlockSimulation code label) :
    Simulation (lifted.program.sem (dialect code)) (P.sem D) (L.StateRel code c₀)
      (L.RetRel code c₀) := by
  refine Simulation.of_blocks fun label arguments store stack ⟨l, ls⟩ ⟨c, hrel, hstack⟩ => ?_
  have hm := h label c arguments store l hrel
  change ((P.runBlock D ⟨label, arguments, store⟩).next D stack).MatchedBy _ _ _ _
  generalize P.runBlock D ⟨label, arguments, store⟩ = t at hm
  cases t with
  | jump u =>
    obtain ⟨l', hr, hrel'⟩ := hm
    exact ⟨⟨l', ls⟩, hr.reaches ls, c, hrel', hstack⟩
  | call u uf =>
    obtain ⟨l₁, hr, hc⟩ := hm
    cases hs : lifted.program.runBlock (dialect code) l₁ with
    | call l' lf =>
      rw [hs] at hc
      obtain ⟨c', hrel', hres⟩ := hc
      refine ⟨⟨l', lf :: ls⟩, (hr.reaches ls).tail ?_, c', hrel', c, hres, hstack⟩
      show (lifted.program.runBlock (dialect code) l₁).next (dialect code) ls = _
      rw [hs]
      rfl
    | jump _ | returned _ | stuck => rw [hs] at hc; exact hc.elim
  | returned uo =>
    obtain ⟨l₁, hr, hc⟩ := hm
    cases hs : lifted.program.runBlock (dialect code) l₁ with
    | returned lo =>
      rw [hs] at hc
      cases stack with
      | nil =>
        cases ls with
        | nil =>
          cases hstack
          refine ⟨lo, (hr.reaches []).exec (.ret ?_), hc⟩
          show (lifted.program.runBlock (dialect code) l₁).next (dialect code) [] = _
          rw [hs]
          rfl
        | cons _ _ => exact hstack.elim
      | cons uf us =>
        cases ls with
        | nil => exact hstack.elim
        | cons lf ls =>
          obtain ⟨c', hres, hstack'⟩ := hstack
          show (if uf.Accepts D uo.tag then Outcome.next ⟨uf.resume uo, us⟩ else .stuck).MatchedBy
            _ _ _ _
          split
          · obtain ⟨hacc, hrel'⟩ := hres uo lo hc ‹_›
            refine ⟨⟨lf.resume lo, ls⟩, (hr.reaches (lf :: ls)).tail ?_, c', hrel', hstack'⟩
            show (lifted.program.runBlock (dialect code) l₁).next (dialect code) (lf :: ls) = _
            rw [hs]
            simp only [Transfer.next, hacc, ↓reduceIte]
          · trivial
    | jump _ | call _ _ | stuck => rw [hs] at hc; exact hc.elim
  | stuck => trivial

theorem Layout.machine [Bindings] {L : Layout P D lifted Ctx} {code : CodeMap} {c₀ : Ctx}
    {boundary : ReturnBoundary}
    (hlifted : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (h : ∀ label, L.BlockSimulation code label) :
    Simulation (machineAnyReturn boundary) (P.sem D)
      (fun u s => ∃ l, L.StateRel code c₀ u l ∧ Lift.Rel code lifted l s)
      (fun uo t => ∃ lo, L.RetRel code c₀ uo lo ∧ Lift.RetRel code lifted lo t) :=
  hlifted.trans (L.simulation code c₀ h)

end P256.Proofs.Refine
