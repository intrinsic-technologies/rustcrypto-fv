import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Parser.ReadSlice

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field

abbrev AdvancesBlock [Bindings] (boundary : ReturnBoundary) (pre : RamState → Prop)
    (code : CodeMap) (effect : RamState → Effect) : Prop :=
  AdvanceTriple boundary pre code (Effect.post effect)

theorem blockThen [Bindings] {boundary : ReturnBoundary} {P pre : RamState → Prop}
    {code code₂ : CodeMap} {E e E' : RamState → Effect}
    (k : AdvancesBlock boundary P code (Effect.seq E e) → AdvancesBlock boundary P code E')
    (step : StepEffect pre code₂ e) (loc : Effect.Local e)
    (sub : ∀ x ∈ code₂, x ∈ code)
    (full : ∀ s, P s → ∀ w ∈ (E s).writes, w.Full)
    (mid : ∀ s t, P s → (E s).Holds s t → (∀ b, Obs ((E s).after s b) t) →
      pre t ∧ (e t).Avoids code)
    (next : ∀ t, pre t → (e t).rip ≠ boundary.rip) :
    AdvancesBlock boundary P code E → AdvancesBlock boundary P code E' := by
  apply AdvanceTriple.block_then k step loc sub full
  intro s t hp he ho
  obtain ⟨ht, ha⟩ := mid s t hp he ho
  exact ⟨ht, ha, next t ht⟩

macro "slice_run_begin " t:term : tactic => `(tactic| (
  refine P256.Proofs.Common.Field.AdvanceTriple.block_first ?k $t ?sub ?pre ?av ?boundary
  try (case sub => x86_sub)
  try (case pre => solve | x86_carry_begin)
  try (case av => solve | x86_carry_av)
  case' k => x86_norm))

macro "slice_run_then " t:term : tactic => `(tactic| (
  refine blockThen ?k $t ?loc ?sub ?full ?mid ?boundary
  try (case loc => x86_local)
  try (case sub => x86_sub)
  try (case full => x86_full)
  try (case mid => solve | x86_mid)
  case' k => x86_norm))

theorem taken_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8)
    (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2 ^ 32) :
    StepEffect (fun s ↦ s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (fun _ ↦ jmpEffect p 2 (disp.signExtend 64)) := by
  intro s hReady hCode hPre
  obtain ⟨t, hStep, hReady', hEffect⟩ :=
    jcc_rel8_effect_step p cc disp s hReady hCode ⟨hPre.1, fun _ ↦ htarget⟩
  exact ⟨t, hStep, hReady', jccEffect_taken hPre.2 hEffect⟩

theorem not_taken_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8) :
    StepEffect (fun s ↦ s.RIP = p ∧
      condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (fun _ ↦ nopEffect p 2) := by
  intro s hReady hCode hPre
  obtain ⟨t, hStep, hReady', hEffect⟩ :=
    jcc_rel8_effect_step p cc disp s hReady hCode ⟨hPre.1, fun hc ↦ by
      rw [hPre.2] at hc
      contradiction⟩
  exact ⟨t, hStep, hReady', jccEffect_not_taken hPre.2 hEffect⟩


end P256.Proofs.SignatureFromDer.Parser.ReadSlice
