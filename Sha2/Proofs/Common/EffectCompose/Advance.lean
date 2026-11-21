import Sha2.Proofs.Common.EffectCompose
import Sha2.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

open Sha2.Proofs.Common.EffectCompose (FlagsAgree)

namespace Sha2.Proofs.Common.Field.AdvanceTriple

open X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {boundary : ReturnBoundary} {P pre₂ : RamState → Prop}
  {code code₂ : CodeMap} {E e₂ : RamState → Effect}
  {Q : RamState → RamState → Prop}

theorem seq_block_on (block : AdvanceTriple boundary P code (Effect.post E))
    (step : StepEffect pre₂ code₂ e₂) (flags : List StatusFlag) (locality : Sha2.Proofs.Common.EffectCompose.Effect.LocalOn flags e₂)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (known : ∀ s, P s → ∀ i ∈ flags, (E s).flag s i ≠ none)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      (∀ b, FlagsAgree flags ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code ∧ (e₂ t).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post (Effect.seq E e₂)) := by
  intro s ready loaded pre
  obtain ⟨fuel, t, run, ready', loaded', effect⟩ := block s ready loaded pre
  obtain ⟨pre', avoid, next⟩ := mid s t pre effect (effect.obsAfter (full s pre))
    ((Sha2.Proofs.Common.EffectCompose.Effect.Holds.knownFlags_after (h := effect)) flags (known s pre))
  obtain ⟨u, run', ready'', effect'⟩ := step.advances ready' (loaded'.mono sub) pre' next
  exact ⟨fuel + 1, u, run.trans run', ready'', effect'.codeIn avoid loaded',
    (Sha2.Proofs.Common.EffectCompose.Effect.Holds.seq_on (h₁ := effect)) flags locality (known s pre) (full s pre) effect'⟩

theorem block_then_on (k : AdvanceTriple boundary P code (Effect.post (fun s => Effect.seq E e₂ s)) →
      AdvanceTriple boundary P code Q)
    (step : StepEffect pre₂ code₂ e₂) (flags : List StatusFlag) (locality : Sha2.Proofs.Common.EffectCompose.Effect.LocalOn flags e₂)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (known : ∀ s, P s → ∀ i ∈ flags, (E s).flag s i ≠ none)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      (∀ b, FlagsAgree flags ((E s).after s b) t) →
      pre₂ t ∧ (e₂ t).Avoids code ∧ (e₂ t).rip ≠ boundary.rip) :
    AdvanceTriple boundary P code (Effect.post E) → AdvanceTriple boundary P code Q :=
  fun block => k (block.seq_block_on step flags locality sub full known mid)

end Sha2.Proofs.Common.Field.AdvanceTriple

macro "advance_mid_on" : tactic => `(tactic| (
  intro s s' hP hH hO hF
  refine ⟨?_, X86Proofs.Effect.LocalOn.avoids (by simp (config := { decide := true }) only [x86_local_on])
    (hO true) (hF true) ?_, ?_⟩
  · first
    | exact hH.rip_of (by x86_norm)
    | exact ⟨hH.rip_of (by x86_norm)⟩
    | (refine X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_; x86_norm; x86_frame)
    | (refine X86Proofs.StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_ <;>
         x86_norm <;> x86_frame)
  · x86_avoid
  · x86_norm
    assumption))

macro "advance_then_on " flags:term " using " step:term : tactic => `(tactic| (
  refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then_on
    ?k $step $flags ?loc ?sub ?full ?known ?mid
  try (case loc => simp (config := { decide := true }) only [x86_local_on])
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case known =>
    intro s hP i hi
    simp only [List.mem_singleton] at hi
    subst i
    x86_norm)
  try (case mid => advance_mid_on)
  case' k => x86_norm))
