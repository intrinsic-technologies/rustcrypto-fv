import Sha2.Proofs.Common.SHA256.Blocks.Absorb
import Sha2.Proofs.Common.SHA256.Absorb.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

def Basic : Block → Prop
  | .prepare registers => [registers.tail, registers.length, registers.remaining, 2].Pairwise (· ≠ ·)
  | .address _ address => address.Valid
  | .splitTail source rest => [source, rest, 0, 1].Pairwise (· ≠ ·)
  | .loadPair .. | .loadTail .. | .storeTail .. | .clearTail .. |
    .incrementBlocks .. | .addBlocks .. | .clone | .spill .. |
    .compareIndexStack .. | .compareZeroStack .. => False
  | _ => True

instance (b : Block) : Decidable (Basic b) := by
  cases b <;> unfold Basic <;> infer_instance

theorem Basic.pre {b : Block} (basic : Basic b) (p : BitVec 64) (s : RamState)
    (rip : s.RIP = p) : Pre p b s := by
  cases b <;> simp_all [Basic, Pre]
  all_goals constructor <;> simp_all

theorem Basic.avoids {b : Block} (basic : Basic b) (p : BitVec 64) (s : RamState)
    (code : CodeMap) : (effect p b s).Avoids code := by
  apply Effect.Avoids.of_noMem
  cases b <;> simp_all [Basic, effect, Effect.components, Component.Covers,
    movR64R64Effect, testR64R64Effect, jccEffect, branchEffect, jmpEffect,
    leaR64Effect, movR32Imm32Effect, incR64Effect, cmpR64R64Effect,
    Common.Instructions.AddByte.addR8R8Effect, addR64Imm8Effect, xorR32R32Effect]

def SiteTrace : List Site → RamState → RamState → Prop
  | [], s, t => t = s
  | site :: rest, s, t =>
      if s.RIP = site.pc then
        ∃ u, (effect site.pc site.block s).Holds s u ∧ SiteTrace rest u t
      else SiteTrace rest s t

def SitePre (code : CodeMap) : List Site → RamState → Prop
  | [], _ => True
  | site :: rest, s =>
      if s.RIP = site.pc then
        Pre site.pc site.block s ∧ (effect site.pc site.block s).Avoids code ∧
          ∀ u, (effect site.pc site.block s).Holds s u → SitePre code rest u
      else SitePre code rest s

theorem SitePre.of_invariant (code : CodeMap) (sites : List Site) (I : RamState → Prop)
    (pre : ∀ site ∈ sites, ∀ s, I s → s.RIP = site.pc → Pre site.pc site.block s)
    (avoid : ∀ site ∈ sites, ∀ s, I s → (effect site.pc site.block s).Avoids code)
    (keep : ∀ site ∈ sites, ∀ s t, I s → (effect site.pc site.block s).Holds s t → I t)
    {s : RamState} (initial : I s) : SitePre code sites s := by
  induction sites generalizing s with
  | nil => trivial
  | cons site rest ih =>
    simp only [SitePre]
    split
    · rename_i hip
      refine ⟨pre site (by simp) s initial hip, avoid site (by simp) s initial, ?_⟩
      intro t step
      exact ih (fun p hp => pre p (List.mem_cons_of_mem site hp))
        (fun p hp => avoid p (List.mem_cons_of_mem site hp))
        (fun p hp => keep p (List.mem_cons_of_mem site hp))
        (keep site (by simp) s t initial step)
    · exact ih (fun p hp => pre p (List.mem_cons_of_mem site hp))
        (fun p hp => avoid p (List.mem_cons_of_mem site hp))
        (fun p hp => keep p (List.mem_cons_of_mem site hp)) initial

theorem SitePre.of_basic (code : CodeMap) (sites : List Site)
    (basic : ∀ site ∈ sites, Basic site.block) (s : RamState) : SitePre code sites s := by
  apply SitePre.of_invariant code sites (fun _ => True)
  · intro site member u _ rip
    exact (basic site member).pre site.pc u rip
  · intro site member u _
    exact (basic site member).avoids site.pc u code
  · intros; trivial
  · trivial

theorem run_sites [Bindings] (boundary : ReturnBoundary) (sites : List Site)
    (code : CodeMap) (stride : Prelude.UnitStringStride (inferInstance : Bindings))
    (outside : ¬ InProgram boundary.rip)
    (inside : ∀ site ∈ sites, BlockInProgram site.pc (bytes site.block).length)
    (targets : ∀ site ∈ sites, match site.block with
      | .branch _ disp | .jump disp =>
        InProgram (branchTarget site.pc (bytes site.block).length disp.value)
      | _ => True)
    (included : ∀ site ∈ sites, ∀ x ∈ site.code, x ∈ code) :
    AdvanceTriple boundary (SitePre code sites) code (SiteTrace sites) := by
  induction sites with
  | nil =>
    intro s ready loaded _
    exact ⟨0, s, by simp, ready, loaded, rfl⟩
  | cons site rest ih =>
    intro s ready loaded pre
    have insideRest := fun p hp => inside p (List.mem_cons_of_mem site hp)
    have targetsRest := fun p hp => targets p (List.mem_cons_of_mem site hp)
    have includedRest := fun p hp => included p (List.mem_cons_of_mem site hp)
    have tail := ih insideRest targetsRest includedRest
    by_cases atSite : s.RIP = site.pc
    · have hp : Pre site.pc site.block s ∧ (effect site.pc site.block s).Avoids code ∧
          ∀ u, (effect site.pc site.block s).Holds s u → SitePre code rest u := by
        simpa only [SitePre, atSite, ite_true] using pre
      obtain ⟨m, u, run, readyU, _, step⟩ :=
        run boundary site.pc site.block stride outside (inside site (by simp))
          (by have ht := targets site (by simp); split <;> simp_all) s ready (loaded.mono (included site (by simp))) hp.1
      have loadedU := step.codeIn hp.2.1 loaded
      obtain ⟨n, t, tailRun, readyT, loadedT, trace⟩ := tail u readyU loadedU (hp.2.2 u step)
      exact ⟨m + n, t, run.trans tailRun, readyT, loadedT,
        by simpa only [SiteTrace, atSite, ite_true] using (⟨u, step, trace⟩ :
          ∃ u, (effect site.pc site.block s).Holds s u ∧ SiteTrace rest u t)⟩
    · have hp : SitePre code rest s := by simpa only [SitePre, atSite, ite_false] using pre
      obtain ⟨n, t, run, readyT, loadedT, trace⟩ := tail s ready loaded hp
      exact ⟨n, t, run, readyT, loadedT, by simpa only [SiteTrace, atSite, ite_false] using trace⟩

theorem stage_of_sites [Bindings] (boundary : ReturnBoundary) (l : Layout)
    (stage : Stage) (sp : BitVec 64) (sites : List Site)
    (stride : Prelude.UnitStringStride (inferInstance : Bindings))
    (outside : ¬ InProgram boundary.rip)
    (inside : ∀ site ∈ sites, BlockInProgram site.pc (bytes site.block).length)
    (targets : ∀ site ∈ sites, match site.block with
      | .branch _ disp | .jump disp =>
        InProgram (branchTarget site.pc (bytes site.block).length disp.value)
      | _ => True)
    (included : ∀ site ∈ sites, ∀ x ∈ site.code, x ∈ stage.code l)
    (pre : ∀ s, stage.Pre l sp s → SitePre (stage.code l) sites s)
    (normalize : ∀ s t, stage.Pre l sp s → SiteTrace sites s t →
      (stage.effect l sp s).Holds s t) :
    AdvanceTriple boundary (stage.Pre l sp) (stage.code l) (Effect.post (stage.effect l sp)) := by
  intro s ready loaded hp
  obtain ⟨fuel, t, run, readyT, loadedT, trace⟩ :=
    run_sites boundary sites (stage.code l) stride outside inside targets included s ready loaded (pre s hp)
  exact ⟨fuel, t, run, readyT, loadedT, normalize s t hp trace⟩

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
