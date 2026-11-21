import Sha2.Proofs.Common.SHA256.Instances.Absorb.Normalize
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Code

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

attribute [local x86_compose] Blocks.effect Blocks.readReg Blocks.bytes jccEffect branchEffect condHolds

private theorem count_local (pc : BitVec 64) (r : BitVec 4) :
    Effect.Local (Blocks.effect pc (.count r)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp [Blocks.effect, Blocks.readReg, shrFlags, h.read_reg]
  · intro s
    simp [Blocks.effect, Write.Full, Operand.Full]

private theorem nextEffect_writes_full (site : Blocks.Site) (E : RamState → Effect)
    (before : ∀ s w, w ∈ (E s).writes → w.Full)
    (step : ∀ s w, w ∈ (Blocks.effect site.pc site.block s).writes → w.Full) :
    ∀ s w, w ∈ (Blocks.nextEffect site E s).writes → w.Full := by
  intro s w hw
  unfold Blocks.nextEffect at hw
  split at hw
  · simp only [Effect.seq, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨w', hw', rfl⟩ | hw
    · exact before s w' (List.mem_filter.mp hw').1
    · exact step _ w hw
  · exact before s w hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem Loop.emptySetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .emptySetup (loop.chunk v) sp)
      (Stage.code .emptySetup (loop.chunk v))
      (Effect.post (Stage.effect .emptySetup (loop.chunk v) sp))  := by
  apply Blocks.stage_of_sites boundary (loop.chunk v) .emptySetup sp
    ((loop.chunk v).blocks .emptySetup) stride outside
  · exact loop.chunk_inside .emptySetup v
  · intro site member
    exact loop.site_targets v site (loop.chunk_sites .emptySetup v site member)
  · intro site member x hx
    exact List.mem_flatMap.mpr ⟨site, member, hx⟩
  · intro s _
    exact Blocks.SitePre.of_basic _ _ (loop.basic_sites .emptySetup (by decide) v) s
  · cases loop
    case' resetDiscarded => let loop : Loop := .resetDiscarded
    case' resetFirst => let loop : Loop := .resetFirst
    case' resetLast => let loop : Loop := .resetLast
    case' finalizeFirst => let loop : Loop := .finalizeFirst
    case' finalizeLast => let loop : Loop := .finalizeLast
    case' traitFirst => let loop : Loop := .traitFirst
    case' traitLast => let loop : Loop := .traitLast
    all_goals
      cases v
      case' sha224 => let v : Wrapper.Variant := .sha224
      case' sha256 => let v : Wrapper.Variant := .sha256
    all_goals
      intro s t pre trace
      have rip := pre.rip
      dsimp only [loop, v, Loop.chunk, Loop.stagePC] at rip
      have composable : Blocks.Composable (Stage.Pre .emptySetup (loop.chunk v) sp)
          ((loop.chunk v).blocks .emptySetup) Effect.start := by
        conv => arg 2; cbv
        simp only [Blocks.Composable]
        repeat' apply And.intro
        all_goals first | trivial | skip
        all_goals
          intro s u t pre before atSite step
          have rip := pre.rip
          dsimp only [loop, v, Loop.chunk, Loop.stagePC] at rip
          first
          | exact before.seq (by exact movR64R64Effect_local)
              (by x86_norm [Blocks.nextEffect, rip]) step
          | exact before.seq (by exact count_local _ _)
              (by x86_norm [Blocks.nextEffect, rip]) step
          | exact before.seq (by exact jmpEffect_local)
              (by
                apply nextEffect_writes_full _ _ ?_ ?_ s
                all_goals repeat' apply nextEffect_writes_full
                all_goals intro s w hw
                all_goals simp only [Effect.start, Blocks.effect, jccEffect, branchEffect,
                  movR64R64Effect, List.mem_singleton, List.not_mem_nil] at hw
                all_goals subst w; trivial) step
          | exact Common.EffectCompose.Effect.Holds.seq_on [.ZF]
              (by exact Blocks.branch_localOn _ _ 5 _ (.inr (.inr rfl)))
              (by intro flag hf; simp only [List.mem_singleton] at hf; subst flag
                  x86_norm [Blocks.nextEffect, rip])
              (by x86_norm [Blocks.nextEffect, rip]) before step
      have result := trace.normalized composable pre
      conv at result => arg 1; arg 1; cbv
      first
      | have buffer := pre.bufferRegister 3 (by decide +kernel)
      | have buffer : True := trivial
      try dsimp only [loop, v, Loop.chunk, Layout.buffer, Blocks.readReg] at buffer
      try x86_norm at buffer
      by_cases zero : Blocks.readReg s (loop.chunk v).registers.length >>> 6 = 0
      all_goals
        dsimp [loop, v, Loop.chunk, Blocks.readReg] at zero
        dsimp only [loop, v, Loop.chunk, Loop.sites, Loop.stageSites, Loop.stagePC,
          Stage.effect, Layout.buffer, Blocks.foldEffect] at ⊢
        x86_norm [Blocks.foldEffect, Blocks.nextEffect, rip, zero, buffer] at result
        repeat' (conv at result => pattern Blocks.Displacement.value _; cbv)
        x86_norm [zero] at result
        apply result.weaken
        · x86_norm [Option.toList, zero, buffer]
        · x86_norm [Option.toList, zero, buffer]
        · intro flag; left; cases flag <;> rfl
        · x86_norm [Option.toList, zero, buffer]
end Sha2.Proofs.Common.SHA256.Instances.Absorption
