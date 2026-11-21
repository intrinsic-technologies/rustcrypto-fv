import X86Proofs.Program.Execution
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Field

open X86 X86.Machine X86.UserProcess X86Proofs

def AdvanceTriple [Bindings] (boundary : ReturnBoundary) (pre : RamState → Prop)
    (code : CodeMap) (post : RamState → RamState → Prop) : Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s →
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧ post s t

namespace AdvanceTriple

variable [Bindings] {boundary : ReturnBoundary} {P pre₁ pre₂ : RamState → Prop}
  {code code₁ code₂ : CodeMap} {E E' e₁ e₂ : RamState → Effect}
  {Q : RamState → RamState → Prop}

theorem of_effect (step : StepEffect P code E)
    (avoid : ∀ s, P s → (E s).Avoids code)
    (next : ∀ s, P s → (E s).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post E) := by
  intro s ready loaded pre
  obtain ⟨t, run, ready', effect⟩ := step.advances ready loaded pre (next s pre)
  exact ⟨1, t, run, ready', effect.codeIn (avoid s pre) loaded, effect⟩

theorem first (step : StepEffect pre₁ code₁ e₁)
    (sub : ∀ x ∈ code₁, x ∈ code) (pre : ∀ s, P s → pre₁ s)
    (avoid : ∀ s, P s → (e₁ s).Avoids code)
    (next : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post e₁) := by
  intro s ready loaded hP
  obtain ⟨t, run, ready', effect⟩ := step.advances ready (loaded.mono sub)
    (pre s hP) (next s hP)
  exact ⟨1, t, run, ready', effect.codeIn (avoid s hP) loaded, effect⟩

theorem seq {mid : RamState → Prop} {post₁ post₂ : RamState → RamState → Prop}
    (left : AdvanceTriple boundary P code post₁)
    (right : AdvanceTriple boundary mid code post₂)
    (pre : ∀ s t, P s → post₁ s t → mid t) :
    AdvanceTriple boundary P code (fun s u => ∃ t, post₁ s t ∧ post₂ t u) := by
  intro s ready loaded hP
  obtain ⟨m, t, run, ready', loaded', hleft⟩ := left s ready loaded hP
  obtain ⟨n, u, run', ready'', loaded'', hright⟩ := right t ready' loaded' (pre s t hP hleft)
  exact ⟨m + n, u, run.trans run', ready'', loaded'', t, hleft, hright⟩

theorem seq_block (block : AdvanceTriple boundary P code (Effect.post E))
    (step : StepEffect pre₂ code₂ e₂) (locality : Effect.Local e₂)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code ∧ (e₂ t).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post (Effect.seq E e₂)) := by
  intro s ready loaded pre
  obtain ⟨fuel, t, run, ready', loaded', effect⟩ := block s ready loaded pre
  obtain ⟨pre', avoid, next⟩ := mid s t pre effect (effect.obsAfter (full s pre))
  obtain ⟨u, run', ready'', effect'⟩ := step.advances ready' (loaded'.mono sub) pre' next
  exact ⟨fuel + 1, u, run.trans run', ready'', effect'.codeIn avoid loaded',
    effect.seq locality (full s pre) effect'⟩

theorem block_first (k : AdvanceTriple boundary P code (Effect.post (fun s => e₁ s)) →
      AdvanceTriple boundary P code Q)
    (step : StepEffect pre₁ code₁ e₁)
    (sub : ∀ x ∈ code₁, x ∈ code) (pre : ∀ s, P s → pre₁ s)
    (avoid : ∀ s, P s → (e₁ s).Avoids code)
    (next : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code Q :=
  k (first step sub pre avoid next)

theorem block_then (k : AdvanceTriple boundary P code (Effect.post (fun s => Effect.seq E e₂ s)) →
      AdvanceTriple boundary P code Q)
    (step : StepEffect pre₂ code₂ e₂) (locality : Effect.Local e₂)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code ∧ (e₂ t).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post E) → AdvanceTriple boundary P code Q :=
  fun block => k (block.seq_block step locality sub full mid)

theorem conseq (block : AdvanceTriple boundary P code Q)
    (post : ∀ s t, P s → Q s t → (E' s).Holds s t) :
    AdvanceTriple boundary P code (Effect.post E') := by
  intro s ready loaded pre
  obtain ⟨fuel, t, run, ready', loaded', result⟩ := block s ready loaded pre
  exact ⟨fuel, t, run, ready', loaded', post s t pre result⟩

theorem block_end (post : ∀ s t, P s → (E s).Holds s t → (E' s).Holds s t) :
    AdvanceTriple boundary P code (Effect.post E) →
      AdvanceTriple boundary P code (Effect.post E') :=
  fun block => block.conseq post

end AdvanceTriple

macro "advance_begin " step:term : tactic => `(tactic| (
  refine Hkdf.Proofs.Common.Field.AdvanceTriple.block_first ?k $step ?sub ?pre ?av ?next
  try (case sub => x86_sub)
  try (case pre => intro s hP; (first
    | exact hP.rip | exact ⟨hP.rip⟩ | exact hP | exact hP.1
    | (refine X86Proofs.LoadPre.of_holds (X86Proofs.Effect.start_holds s)
         (X86Proofs.Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
       x86_norm; x86_frame)
    | (refine X86Proofs.StorePre.of_holds (X86Proofs.Effect.start_holds s)
         (X86Proofs.Effect.start_obs s) hP.rip (by x86_addr_obs) ?_ ?_ <;> x86_norm <;> x86_frame)))
  try (case av => intro _ _; x86_avoid)
  try (case next => intro _ _; x86_norm; assumption)
  case' k => x86_norm))

macro "advance_mid" : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨?_, X86Proofs.Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
  · first
    | exact hH.rip_of (by x86_norm)
    | exact ⟨hH.rip_of (by x86_norm)⟩
    | (refine X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_; x86_norm; x86_frame)
    | (refine X86Proofs.StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_ <;>
         x86_norm <;> x86_frame)
  · x86_avoid
  · x86_norm
    assumption))

macro "advance_then " step:term : tactic => `(tactic| (
  refine Hkdf.Proofs.Common.Field.AdvanceTriple.block_then
    ?k $step ?loc ?sub ?full ?mid
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid => advance_mid)
  case' k => x86_norm))

syntax "advance_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| advance_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply Hkdf.Proofs.Common.Field.AdvanceTriple.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
        all_goals (try (repeat constructor <;> rfl))
      · x86_norm [$ls,*]
        all_goals (try (repeat constructor <;> rfl))
      · intro i; cases i <;> x86_norm [$ls,*]
        all_goals (try (repeat constructor <;> rfl))
      · x86_norm [$ls,*]
        all_goals (try (repeat constructor <;> rfl))))

end Hkdf.Proofs.Common.Field
