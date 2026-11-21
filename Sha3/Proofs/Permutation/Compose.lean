import Sha3.Proofs.Run
import X86Proofs.Program.Compose

namespace X86Proofs.AdvanceTriple

open X86 X86.Machine X86.UserProcess

variable [Bindings] {boundary : ReturnBoundary} {m n : Nat}
  {P pre₁ pre₂ : RamState → Prop} {code code₁ code₂ : CodeMap}
  {E E' e₁ e₂ : RamState → Effect}

theorem first (h₁ : StepEffect pre₁ code₁ e₁) (hsub : ∀ x ∈ code₁, x ∈ code)
    (hpre : ∀ s, P s → pre₁ s) (hav : ∀ s, P s → (e₁ s).Avoids code)
    (hne : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvanceTriple boundary 1 P code (Effect.post e₁) :=
  of_effect (h₁.mono_pre hpre) hsub hav hne

theorem seq_block (h₁ : AdvanceTriple boundary m P code (Effect.post E))
    (h₂ : StepEffect pre₂ code₂ e₂) (hl : Effect.Local e₂)
    (hsub : ∀ x ∈ code₂, x ∈ code)
    (hfull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hmid : ∀ s s', P s → (E s).Holds s s' → (∀ b, Obs ((E s).after s b) s') →
      pre₂ s' ∧ (e₂ s').Avoids code)
    (hne : ∀ s s', P s → (E s).Holds s s' → (e₂ s').rip ≠ boundary.rip) :
    AdvanceTriple boundary (m + 1) P code (Effect.post fun s ↦ Effect.seq E e₂ s) := by
  intro s hr hc hP
  obtain ⟨s', hrun, hr', hc', hp⟩ := h₁ s hr hc hP
  obtain ⟨hpre, hav⟩ := hmid s s' hP hp (hp.obsAfter (hfull s hP))
  obtain ⟨s'', hrun', hr'', hp'⟩ := h₂.advances hr' (hc'.mono hsub) hpre (hne s s' hP hp)
  exact ⟨s'', hrun.trans hrun', hr'', hp'.codeIn hav hc', hp.seq hl (hfull s hP) hp'⟩

theorem block_first {Q : RamState → RamState → Prop}
    (k : AdvanceTriple boundary 1 P code (Effect.post fun s ↦ e₁ s) →
      AdvanceTriple boundary n P code Q)
    (h₁ : StepEffect pre₁ code₁ e₁) (hsub : ∀ x ∈ code₁, x ∈ code)
    (hpre : ∀ s, P s → pre₁ s) (hav : ∀ s, P s → (e₁ s).Avoids code)
    (hne : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) : AdvanceTriple boundary n P code Q :=
  k (first h₁ hsub hpre hav hne)

theorem block_then {Q : RamState → RamState → Prop}
    (k : AdvanceTriple boundary (m + 1) P code (Effect.post fun s ↦ Effect.seq E e₂ s) →
      AdvanceTriple boundary n P code Q)
    (h₂ : StepEffect pre₂ code₂ e₂) (hl : Effect.Local e₂)
    (hsub : ∀ x ∈ code₂, x ∈ code) (hfull : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (hmid : ∀ s s', P s → (E s).Holds s s' → (∀ b, Obs ((E s).after s b) s') →
      pre₂ s' ∧ (e₂ s').Avoids code)
    (hne : ∀ s s', P s → (E s).Holds s s' → (e₂ s').rip ≠ boundary.rip) :
    AdvanceTriple boundary m P code (Effect.post E) → AdvanceTriple boundary n P code Q :=
  fun h₁ ↦ k (h₁.seq_block h₂ hl hsub hfull hmid hne)

theorem block_end (h : ∀ s s', P s → (E s).Holds s s' → (E' s).Holds s s') :
    AdvanceTriple boundary m P code (Effect.post E) →
      AdvanceTriple boundary m P code (Effect.post E') :=
  fun h₁ ↦ h₁.conseq (fun _ h ↦ h) h

end X86Proofs.AdvanceTriple

namespace X86Proofs

macro "ax86_begin " t:term : tactic => `(tactic| (
  refine AdvanceTriple.block_first ?k $t ?sub ?pre ?av ?boundary
  try (case sub => x86_sub)
  try (case pre => intro s hP; (first
    | exact hP.rip | exact ⟨hP.rip⟩ | exact hP | exact hP.1
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip ?_
       x86_norm; x86_frame)
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip ?_ ?_ <;>
       x86_norm <;> x86_frame)))
  try (case av => intro _ _; x86_avoid)
  try (case boundary => intro _ _; x86_norm; assumption)
  case' k => x86_norm))

macro "ax86_then " t:term : tactic => `(tactic| (
  refine AdvanceTriple.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid => x86_mid)
  try (case boundary => intro _ _ _ _; x86_norm; assumption)
  case' k => x86_norm))

syntax "ax86_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ax86_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply AdvanceTriple.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
      · x86_norm [$ls,*]
      · intro i; cases i <;> x86_norm [$ls,*]
      · x86_norm [$ls,*]))

end X86Proofs
