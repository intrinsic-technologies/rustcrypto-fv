import Sha2.Proofs.Common.SHA256.Instances.Absorb.Normalize
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Code

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

set_option maxHeartbeats 1200000 in
theorem Loop.memoryStage [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (stage : Stage)
    (memory : stage ∈ [Stage.smallStore, .increment, .clearTail, .addBlocks, .tailStore])
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre stage (loop.chunk v) sp)
      (Stage.code stage (loop.chunk v))
      (Effect.post (Stage.effect stage (loop.chunk v) sp)) := by
  have one : ∃ site, (loop.chunk v).blocks stage = [site] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at memory
    rcases memory with rfl | rfl | rfl | rfl | rfl <;>
      cases loop <;> cases v <;> exact ⟨_, rfl⟩
  obtain ⟨site, single⟩ := one
  have member : site ∈ (loop.chunk v).blocks stage := by rw [single]; simp
  have preSite : ∀ s, Stage.Pre stage (loop.chunk v) sp s → Blocks.Pre site.pc site.block s := by
    intro s pre
    simp only [List.mem_cons, List.not_mem_nil, or_false] at memory
    rcases memory with rfl | rfl | rfl | rfl | rfl <;>
      cases loop <;> cases v
    all_goals have eq := List.singleton_inj.mp single
    all_goals subst site
    all_goals simp only [Blocks.Pre]
    all_goals try (refine ⟨?_, by decide +kernel, by decide +kernel⟩)
    all_goals refine ⟨pre.rip, by decide +kernel, ?_, ?_⟩
    all_goals first
      | simpa [Loop.chunk, Layout.buffer, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr,
        Operand.read, ← pre.rsp, BitVec.add_assoc] using pre.tailWritable
      | simpa [Loop.chunk, Layout.buffer, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr,
        Operand.read, ← pre.rsp, BitVec.add_assoc] using pre.counterWritable
      | simpa [Loop.chunk, Layout.buffer, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr,
        Operand.read, ← pre.rsp, BitVec.add_assoc] using pre.tailApart _ member
      | simpa [Loop.chunk, Layout.buffer, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr,
        Operand.read, ← pre.rsp, BitVec.add_assoc] using pre.counterApart _ member
  intro s ready loaded pre
  have code : CodeIn site.code s := by
    simpa only [Stage.code, single, List.flatMap_cons, List.flatMap_nil, List.append_nil] using loaded
  obtain ⟨fuel, t, run, readyT, loadedT, result⟩ :=
    Blocks.run boundary site.pc site.block stride outside (loop.chunk_inside stage v site member)
      (by have ht := loop.site_targets v site (loop.chunk_sites stage v site member)
          split <;> simp_all) s ready code (preSite s pre)
  refine ⟨fuel, t, run, readyT, ?_, ?_⟩
  · simpa only [Stage.code, single, List.flatMap_cons, List.flatMap_nil, List.append_nil, Blocks.Site.code] using loadedT
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at memory
    rcases memory with rfl | rfl | rfl | rfl | rfl <;>
      cases loop <;> cases v
    all_goals have eq := List.singleton_inj.mp single
    all_goals subst site
    all_goals apply result.weaken
    all_goals
      simp only [Blocks.effect, storeEffect, ↓reduceIte, BitVec.ofNat_eq_ofNat, AddrMode.addr,
        AddrMode.reg64, Operand.read, Int.reduceToNat, Nat.reduceLeDiff, Nat.reducePow,
        Nat.reduceLT, BitVec.setWidth_ofNat_of_le_of_lt, Fin.getElem_fin, BitVec.setWidth_eq,
        Disp.value, BitVec.reduceSignExtend, Stage.effect, chunk, stagePC, Layout.buffer,
        ← pre.rsp, stackPtr, BitVec.add_assoc, BitVec.zero_add, List.mem_cons, List.not_mem_nil,
        or_false, imp_self, implies_true, FlagWeaker, Effect.flag, reduceCtorEq, or_true,
        Effect.components, List.map_cons, Write.component_mem, Nat.zero_lt_succ, Nat.div_self,
        List.map_nil, List.append_nil, List.cons_append, List.nil_append, forall_eq_or_imp,
        true_or, forall_eq, and_self, BitVec.reduceAdd, incMEffect, Nat.reduceDiv, or_self,
        addMREffect, Write.mk.injEq, heq_eq_eq, BitVec.add_right_inj, true_and]
    all_goals first
      | rfl
      | decide +kernel
      | (intro flag; cases flag <;> rfl)
      | (intro flag; cases flag <;> exact Or.inl rfl)

end Sha2.Proofs.Common.SHA256.Instances.Absorption
