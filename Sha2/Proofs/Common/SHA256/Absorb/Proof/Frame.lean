import Sha2.Proofs.Common.SHA256.Absorb.Proof.Geometry
import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Transport

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem Preserved.of_agrees [Bindings] {l : Layout} {initial before s t : RamState}
    {n reserve fuel : Nat} {regions : Vector MemoryRegion n} {components : List Component}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (footprint l (l.sp initial)))
    (registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ l.clobbered → .reg r ∉ components)
    (df : .df ∉ components) : Preserved l initial before t regions := by
  have frame := PhaseFrame.of_agrees agrees writes registers
  exact ⟨Table.execution_of_frame input.state run ready agrees df frame.memory
    ctx.footprint_avoids ctx.within,
    (frame.registers 4 (by decide) ctx.wf.preservesStack).trans input.rsp,
    input.frame.trans frame⟩

theorem Context.stage_writes [Bindings] {l : Layout} {initial s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) (stage : Stage) :
    WritesWithin (stage.effect l (l.sp initial) s).components (footprint l (l.sp initial)) := by
  have tail : ∀ a, (Component.mem (l.buffer (l.sp initial) + 63) 1).Covers a →
      ∃ region ∈ footprint l (l.sp initial), region.Contains a.toNat := by
    intro a covered
    exact ⟨_, by simp [footprint], ctx.buffer_cover (by decide : 63 + 1 ≤ 104) covered⟩
  have counter : ∀ a, (Component.mem (l.buffer (l.sp initial) + 96) 8).Covers a →
      ∃ region ∈ footprint l (l.sp initial), region.Contains a.toNat := by
    intro a covered
    exact ⟨_, by simp [footprint], ctx.buffer_cover (by decide : 96 + 8 ≤ 104) covered⟩
  intro c member a covered
  cases stage <;> cases hsave : l.bulkSave <;> cases hrestore : l.bufferRestore <;>
    simp only [Stage.effect, Blocks.effect, testR64R64Effect, branchEffect,
      Common.Instructions.AddByte.addR8R8Effect, Effect.components,
      List.map_cons, List.map_nil, Write.component, Operand.component,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      hsave, hrestore, Option.toList_none, Option.toList_some, List.append_nil,
      List.nil_append, List.map_append] at member
  all_goals repeat' (rcases member with member | member)
  all_goals first
    | exact tail a covered
    | exact counter a covered
    | exact covered.elim

end Sha2.Proofs.Common.SHA256.Absorb
