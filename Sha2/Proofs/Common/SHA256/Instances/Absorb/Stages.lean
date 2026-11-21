import Sha2.Proofs.Common.SHA256.Instances.Absorb.Normalize
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Code
import Sha2.Proofs.Common.SHA256.Instances.Absorb.StagesMemory
import Sha2.Proofs.Common.SHA256.Instances.Absorb.StagesEmpty

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem Loop.singleBasicStage [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (stage : Stage)
    (single : stage ∈ [Stage.prepare, .smallBranch, .emptyTest, .emptyBranch,
      .smallLength, .restoreSource, .count, .countBranch, .splitTail])
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre stage (loop.chunk v) sp)
      (Stage.code stage (loop.chunk v))
      (Effect.post (Stage.effect stage (loop.chunk v) sp)) := by
  let site := ((loop.chunk v).blocks stage).headD ⟨0, .zero 0⟩
  have singleton : (loop.chunk v).blocks stage = [site] := by
    cases stage <;>
      simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
        or_false, or_true] at single
    all_goals cases loop <;> cases v <;> rfl
  have member : site ∈ (loop.chunk v).blocks stage := by rw [singleton]; simp
  have basic := loop.basic_sites stage (by
    cases stage <;> simp_all) v site member
  have pc : site.pc = (loop.chunk v).pc stage := by
    cases stage <;>
      simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
        or_false, or_true] at single
    all_goals cases loop <;> cases v <;> rfl
  have effects : ∀ s, Blocks.effect site.pc site.block s =
      Stage.effect stage (loop.chunk v) sp s := by
    intro s
    cases stage <;>
      simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
        or_false, or_true] at single
    all_goals cases loop <;> cases v <;>
      (simp only [Blocks.effect, List.headD_eq_head?_getD, Loop.chunk,
        BitVec.ofNat_eq_ofNat, ↓reduceIte,
        Loop.stagePC, Loop.stageSites, Loop.sites, List.mem_cons, List.not_mem_nil, or_false,
        BitVec.reduceEq, decide_false, Bool.false_eq_true, not_false_eq_true,
        List.filter_cons_of_neg, decide_true, List.filter_cons_of_pos, List.filter_nil,
        List.head?_cons, Option.getD_some, Blocks.bytes, List.append_assoc, List.length_append,
        Nat.reduceLeDiff, Nat.reducePow, Nat.reduceLT, BitVec.setWidth_ofNat_of_le_of_lt,
        Stage.effect, Effect.mk.injEq, and_self, and_true, site, reduceCtorEq, jccEffect,
        branchEffect, branchTarget, List.length_cons, immBytes_length, Nat.zero_lt_succ,
        Nat.div_self, Nat.reduceAdd, BitVec.reduceAdd, Blocks.Displacement.value,
        BitVec.reduceSignExtend, testR64R64Effect, Operand.read_reg64, Int.reduceToNat,
        Fin.getElem_fin, BitVec.and_self, Nat.reduceDiv, Common.Instructions.AddByte.addR8R8Effect,
        Operand.read_reg8, movR64R64Effect, List.cons.injEq, Write.mk.injEq, heq_eq_eq, true_and,
        BitVec.setWidth_and] <;> first | rfl | decide +kernel)
  intro s ready loaded pre
  have code : Stage.code stage (loop.chunk v) = site.code := by
    simp only [Stage.code, singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [code] at loaded ⊢
  obtain ⟨fuel, t, run, readyT, loadedT, post⟩ :=
    Blocks.run boundary site.pc site.block stride outside
      (loop.chunk_inside stage v site member)
      (by have targets := loop.site_targets v site (loop.chunk_sites stage v site member)
          split <;> simp_all)
      s ready loaded (basic.pre site.pc s (pre.rip.trans pc.symm))
  exact ⟨fuel, t, run, readyT, loadedT, by simpa only [Effect.post, effects] using post⟩


attribute [local x86_compose] Blocks.effect Blocks.readReg

macro "sha256_absorb_straight_stage" loop:ident v:ident boundary:ident
    stride:ident outside:ident sp:ident stage:term : tactic =>
  `(tactic| first
    |
      apply Blocks.stage_of_sites $boundary (($loop).chunk $v) $stage $sp
        ((($loop).chunk $v).blocks $stage) $stride $outside
      · exact ($loop).chunk_inside $stage $v
      · intro site member
        exact ($loop).site_targets $v site (($loop).chunk_sites $stage $v site member)
      · intro site member x hx
        exact List.mem_flatMap.mpr ⟨site, member, hx⟩
      · intro s _
        exact Blocks.SitePre.of_basic _ _ (($loop).basic_sites $stage (by simp) $v) s
      · have composable : Blocks.Composable (Stage.Pre $stage (($loop).chunk $v) $sp)
            ((($loop).chunk $v).blocks $stage) Effect.start := by
          cases ($loop) <;> cases ($v)
          all_goals
            conv => arg 2; cbv
            simp only [Blocks.Composable]
            repeat' constructor
            all_goals
              intro s u t pre before _ step
              have rip := pre.rip
              exact before.seq (by first
                | exact movR64R64Effect_local
                | exact leaR64Effect_local
                | exact addR64Imm8Effect_local
                | exact movR32Imm32Effect_local)
                (by x86_norm [Option.toList, Blocks.nextEffect, Loop.stagePC, rip]) step
        intro s t pre trace
        have effect := trace.normalized composable pre
        have rip := pre.rip
        have rsp : (.reg 4#5 : Operand 64).read s = $sp := pre.rsp
        have buffer := pre.bufferRegister
        have restored := pre.bufferRestored
        cases ($loop) <;> cases ($v)
        all_goals
          conv at effect => arg 1; arg 1; cbv
          simp only [Loop.chunk, Loop.stagePC] at rip
          simp only [Loop.chunk, BitVec.ofNat_eq_ofNat, ↓reduceIte, Option.mem_def, reduceCtorEq,
            Blocks.readReg, Operand.read_reg64, Int.reduceToNat, Fin.getElem_fin, Layout.buffer,
            BitVec.add_zero, false_implies, implies_true, Option.some.injEq, forall_eq',
            Nat.reduceLeDiff, Nat.reducePow, Nat.reduceLT, BitVec.setWidth_ofNat_of_le_of_lt,
            imp_self, forall_const, true_implies] at buffer restored
          refine ⟨effect.rip.trans ?_, ?_, ?_, effect.agrees.mono ?_⟩
          · x86_norm [Option.toList, Blocks.foldEffect, Blocks.nextEffect, Stage.effect, Loop.chunk,
              Loop.stagePC, rip]
          · have obs := effect.obsAfter (by
              x86_norm [Option.toList, Blocks.foldEffect, Blocks.nextEffect, rip]) true
            apply Write.allHold_iff.mpr
            intro w hw
            simp only [Stage.effect, Loop.chunk, Option.toList_some, Option.toList_none,
              List.map_cons, List.map_nil,
              List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hw
            all_goals first
              | (rcases hw with rfl | rfl | rfl | rfl)
              | (rcases hw with rfl | rfl | rfl)
              | (rcases hw with rfl | rfl)
              | (rcases hw with rfl)
              | contradiction
            all_goals
              try subst w
              apply Eq.trans (obs.read _ (by trivial)).symm
              x86_norm [Option.toList, Blocks.foldEffect, Blocks.nextEffect, Layout.buffer,
                rip, rsp,
                buffer, restored, BitVec.add_zero, BitVec.shiftLeft_zero]
              try (first
                | exact buffer
                | exact restored
                | rfl
                | ac_rfl
                | (change _ = _; simp only [Operand.read, State.regValue]; ac_rfl))
          · trivial
          · x86_norm [Option.toList, Blocks.foldEffect, Blocks.nextEffect, Stage.effect, Loop.chunk,
              Loop.stagePC, rip]

  )

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.smallSetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .smallSetup (loop.chunk v) sp)
      (Stage.code .smallSetup (loop.chunk v))
      (Effect.post (Stage.effect .smallSetup (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .smallSetup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.fillSetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .fillSetup (loop.chunk v) sp)
      (Stage.code .fillSetup (loop.chunk v))
      (Effect.post (Stage.effect .fillSetup (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .fillSetup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.fillCompressSetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .fillCompressSetup (loop.chunk v) sp)
      (Stage.code .fillCompressSetup (loop.chunk v))
      (Effect.post (Stage.effect .fillCompressSetup (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .fillCompressSetup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.bulkSetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .bulkSetup (loop.chunk v) sp)
      (Stage.code .bulkSetup (loop.chunk v))
      (Effect.post (Stage.effect .bulkSetup (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .bulkSetup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.bulkRestore [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .bulkRestore (loop.chunk v) sp)
      (Stage.code .bulkRestore (loop.chunk v))
      (Effect.post (Stage.effect .bulkRestore (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .bulkRestore

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem Loop.tailSetup [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Stage.Pre .tailSetup (loop.chunk v) sp)
      (Stage.code .tailSetup (loop.chunk v))
      (Effect.post (Stage.effect .tailSetup (loop.chunk v) sp)) := by
  sha256_absorb_straight_stage loop v boundary stride outside sp .tailSetup

theorem Loop.blockContracts [bindings : Bindings] (loop : Loop) (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Absorb.BlockContracts (loop.chunk v) boundary := by
  constructor
  intro stage notCall sp
  cases stage <;> simp only [Stage.isCall, Bool.true_eq_false] at notCall
  all_goals first
    | exact loop.singleBasicStage v _ (by decide) boundary stride outside sp
    | exact loop.memoryStage v _ (by decide) boundary stride outside sp
    | exact loop.smallSetup v boundary stride outside sp
    | exact loop.fillSetup v boundary stride outside sp
    | exact loop.fillCompressSetup v boundary stride outside sp
    | exact loop.bulkSetup v boundary stride outside sp
    | exact loop.bulkRestore v boundary stride outside sp
    | exact loop.tailSetup v boundary stride outside sp
    | exact loop.emptySetup v boundary stride outside sp

end Sha2.Proofs.Common.SHA256.Instances.Absorption
