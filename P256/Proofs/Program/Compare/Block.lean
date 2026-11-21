import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Program.Execution
import P256.Proofs.Program.Compare.Instructions.Common

namespace P256.Proofs.Program.Compare.Block

open X86 X86.Machine X86.UserProcess X86Proofs

abbrev AdvancesBlock [Bindings] (boundary : ReturnBoundary) (pre : RamState → Prop)
    (code : CodeMap) (effect : RamState → Effect) : Prop :=
  P256.Proofs.Common.Field.AdvanceTriple boundary pre code (Effect.post effect)

namespace AdvancesBlock

variable [Bindings] {boundary : ReturnBoundary} {P pre₁ pre₂ : RamState → Prop}
  {code code₁ code₂ : CodeMap} {E e₁ e₂ E' : RamState → Effect}

theorem block_first
    (k : AdvancesBlock boundary P code e₁ → AdvancesBlock boundary P code E')
    (step : StepEffect pre₁ code₁ e₁) (sub : ∀ x ∈ code₁, x ∈ code)
    (pre : ∀ s, P s → pre₁ s) (avoid : ∀ s, P s → (e₁ s).Avoids code)
    (next : ∀ s, P s → (e₁ s).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code E' :=
  k (Common.Field.AdvanceTriple.first step sub pre avoid next)

theorem block_then
    (k : AdvancesBlock boundary P code (Effect.seq E e₂) → AdvancesBlock boundary P code E')
    (step : StepEffect pre₂ code₂ e₂) (locality : Effect.Local e₂)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code)
    (next : ∀ t, pre₂ t → (e₂ t).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code E → AdvancesBlock boundary P code E' := by
  intro block
  apply k
  apply Common.Field.AdvanceTriple.seq_block block step locality sub full
  intro s t hp hh ho
  obtain ⟨hm, ha⟩ := mid s t hp hh ho
  exact ⟨hm, ha, next t hm⟩

theorem block_end (post : ∀ s t, P s → (E s).Holds s t → (E' s).Holds s t) :
    AdvancesBlock boundary P code E → AdvancesBlock boundary P code E' :=
  Common.Field.AdvanceTriple.block_end post

end AdvancesBlock

macro "p256_memcmp_block_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  try (case sub => x86_sub)
  try (case pre => intro s hP; (first
    | exact hP.rip | exact ⟨hP.rip⟩ | exact hP | exact hP.1
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
       x86_norm; x86_frame)
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_ ?_ <;>
       x86_norm <;> x86_frame)))
  try (case av => intro _ _; x86_avoid)
  case' k => x86_norm))

macro "p256_memcmp_block_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid => x86_mid)
  case' k => x86_norm))

syntax "p256_memcmp_block_finish" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| p256_memcmp_block_finish $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      apply AdvancesBlock.block_end
      intro s s' _ hH
      apply hH.weaken
      · x86_norm [$ls,*]
      · x86_norm [$ls,*]
      · intro i; cases i <;> x86_norm [$ls,*]
      · x86_norm [$ls,*]))

end P256.Proofs.Program.Compare.Block
