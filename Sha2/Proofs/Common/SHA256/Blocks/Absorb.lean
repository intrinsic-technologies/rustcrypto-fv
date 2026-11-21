import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Variants
import Sha2.Proofs.Common.SHA256.Absorb.Blocks
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Byte
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Sequence
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.LoadPair

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field
open Sha2.Proofs.Common.Instructions

theorem run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (b : Block)
    (stride : Prelude.UnitStringStride (inferInstance : Bindings))
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes b).length)
    (targets : match b with
      | .branch _ disp | .jump disp => InProgram (branchTarget p (bytes b).length disp.value)
      | _ => True) : Contract boundary p b := by
  unfold Contract
  cases b with
  | move dst src =>
    apply AdvanceTriple.of_effect (move_step p dst src)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, movR64R64Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | test r =>
    apply AdvanceTriple.of_effect (test_step p r r)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, testR64R64Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | constant dst value =>
    apply AdvanceTriple.of_effect (constant_step p dst value)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, movR32Imm32Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | incrementIndex r =>
    apply AdvanceTriple.of_effect (increment_step p r)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, incR64Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | compareIndex index count =>
    apply AdvanceTriple.of_effect (compare_step p count index)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, cmpR64R64Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | addTail dst src =>
    apply AdvanceTriple.of_effect (addTail_step p dst src)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, AddByte.addR8R8Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | address dst am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      exact address_step p dst am pre.2 s ready loaded pre.1
    · intro s _
      exact Effect.Avoids.of_noMem (by simp [effect, leaR64Effect, Effect.components,
        Component.Covers]) _
    · intro s _
      apply boundary_ne_program outside
      have len : (bytes (.address dst am)).length = 3 + am.tail.length := by
        simp only [bytes, encodeLeaR64M, List.length_cons]
        omega
      change InProgram (p + BitVec.ofNat 64 (3 + am.tail.length))
      simpa only [len] using inside _ (Nat.le_refl _)
  | loadTail r am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      exact loadTail_step p r am pre.valid s ready loaded ⟨pre.rip, pre.readable⟩
    · intro s _
      exact Effect.Avoids.of_noMem (by simp [effect, Effect.components, Component.Covers]) _
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | storeTail r am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      exact storeTail_step p r am pre.valid s ready loaded
        ⟨pre.rip, pre.writable.toMemWritable, pre.apart⟩
    · intro s pre
      apply Effect.avoids_of_mem (addr := am.addr s
        (p + BitVec.ofNat 64 (bytes (.storeTail r am)).length)) (len := 1) _ pre.apart rfl
      simp [effect, storeEffect, Effect.components, Component.isMem]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | clearTail am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      have len : (bytes (.clearTail am)).length = 3 + am.tail.length := by
        simp only [bytes, List.length_append, List.length_cons, List.length_nil]
        omega
      have step := mov_m8_imm8_effect_step p am pre.1.valid pre.2.1 pre.2.2 0
      have code : bytes (.clearTail am) = 0xc6 :: am.modrm 0 :: (am.tail ++ immBytes 8 0) := rfl
      rw [← code] at step
      simpa only [effect, len, movM8Imm8Effect, storeAddrAt, BitVec.signExtend_eq] using
        step s ready loaded ⟨pre.1.rip, by simpa only [len] using pre.1.writable.toMemWritable,
          by simpa only [len] using pre.1.apart⟩
    · intro s pre
      apply Effect.avoids_of_mem (addr := am.addr s
        (p + BitVec.ofNat 64 (bytes (.clearTail am)).length)) (len := 1) _ pre.1.apart rfl
      simp [effect, storeEffect, Effect.components, Component.isMem]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | incrementBlocks am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      obtain ⟨hrex, _, hx, hb⟩ := am.rexByte_true_spec 0
      have step := inc_m64_effect_step p _ hrex am pre.valid hx hb
      have len : (bytes (.incrementBlocks am)).length = 3 + am.tail.length := by
        simp only [bytes, encodeIncM64, List.length_cons]
        omega
      simpa only [effect, len] using step s ready loaded
        ⟨pre.rip, by simpa only [len] using pre.writable.toMemWritable,
          by simpa only [len] using pre.apart⟩
    · intro s pre
      apply Effect.avoids_of_mem (addr := am.addr s
        (p + BitVec.ofNat 64 (bytes (.incrementBlocks am)).length)) (len := 8) _ pre.apart rfl
      rw [effect, incMEffect_components]
      exact mem_components_rmw _ _
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | addBlocks am =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec 2
      have step := add_m64_r64_effect_step p _ hrex (regLow 2) am pre.valid hx hb
      rw [hr, gprNumber_reg] at step
      have register : (2 : BitVec 4).setWidth 5 = (2 : BitVec 5) := by decide +kernel
      rw [register] at step
      have len : (bytes (.addBlocks am)).length = 3 + am.tail.length := by
        simp only [bytes, encodeAddM64R64, List.length_cons]
        omega
      simpa only [effect, len] using step s ready loaded
        ⟨pre.rip, by simpa only [len] using pre.writable.toMemWritable,
          by simpa only [len] using pre.apart⟩
    · intro s pre
      apply Effect.avoids_of_mem (addr := am.addr s
        (p + BitVec.ofNat 64 (bytes (.addBlocks am)).length)) (len := 8) _ pre.apart rfl
      rw [effect, addMREffect_components]
      exact mem_components_rmw _ _
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | branch cc disp =>
    have targetLow : (branchTarget p (bytes (.branch cc disp)).length disp.value).toNat < 2^32 := by
      obtain ⟨byte, mem⟩ := targets
      exact programSections_low.codeLow (_, byte) mem
    cases disp with
    | short displacement =>
      apply AdvanceTriple.of_effect
      · intro s ready loaded rip
        exact jcc_rel8_effect_step p cc displacement s ready loaded ⟨rip, fun _ => targetLow⟩
      · intro s _
        exact branchEffect_avoids _ _ _ _
      · intro s _
        change (if _ then _ else _) ≠ _
        split
        · exact boundary_ne_program outside targets
        · exact boundary_ne_program outside (inside _ (Nat.le_refl _))
    | near displacement =>
      apply AdvanceTriple.of_effect
      · intro s ready loaded rip
        exact jcc_rel32_effect_step p cc displacement s ready loaded ⟨rip, fun _ => targetLow⟩
      · intro s _
        exact branchEffect_avoids _ _ _ _
      · intro s _
        change (if _ then _ else _) ≠ _
        split
        · exact boundary_ne_program outside targets
        · exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | jump disp =>
    have targetLow : (branchTarget p (bytes (.jump disp)).length disp.value).toNat < 2^32 := by
      obtain ⟨byte, mem⟩ := targets
      exact programSections_low.codeLow (_, byte) mem
    cases disp with
    | short displacement =>
      apply AdvanceTriple.of_effect (jmp_rel8_effect_step p displacement targetLow)
      · intro s _
        exact jmpEffect_avoids _ _ _ _
      · intro s _
        exact boundary_ne_program outside targets
    | near displacement =>
      apply AdvanceTriple.of_effect (jmp_rel32_effect_step p displacement targetLow)
      · intro s _
        exact jmpEffect_avoids _ _ _ _
      · intro s _
        exact boundary_ne_program outside targets
  | clone =>
    intro s ready loaded pre
    have start := inside 0 (by decide)
    change InProgram (p + 0#64) at start
    rw [BitVec.add_zero] at start
    have execution := RepMovsq.rep_movsq_execution stride ready loaded pre.1 pre.2
      (boundary_ne_program outside start)
      (boundary_ne_program outside (inside 3 (by decide)))
    refine ⟨13, nextStates 13 s, execution.1, execution.2.1, ?_, execution.2.2.1⟩
    exact execution.2.2.1.codeIn (repMovsqEffect_avoids 0x48 pre.1.dstCode) loaded
  | loadPair index source length pointers lengths =>
    exact loadPair_run boundary p index source length pointers lengths outside inside
  | prepare registers => exact prepare_run boundary p registers outside inside
  | count remaining => exact count_run boundary p remaining outside inside
  | splitTail source remaining => exact splitTail_run boundary p source remaining outside inside

  | addImmediate dst value =>
    apply AdvanceTriple.of_effect (addImmediate_step p dst value)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, addR64Imm8Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | zero dst =>
    apply AdvanceTriple.of_effect (zero_step p dst)
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [Effect.components, xorR32R32Effect, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | compareIndexStack index slot =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      apply compareIndexStack_step p index slot pre.valid s ready loaded
      refine ⟨pre.rip, ?_⟩
      simpa [AddrMode.addr, AddrMode.reg64] using pre.readable
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [effect, cmpMREffect, Effect.components, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | compareZeroStack slot value =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      apply compareZeroStack_step p slot value pre.valid s ready loaded
      refine ⟨pre.rip, ?_⟩
      simpa [AddrMode.addr, AddrMode.reg64] using pre.readable
    · intro s _
      apply Effect.Avoids.of_noMem
      simp [effect, cmpMImm8Effect, Effect.components, Component.Covers]
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))
  | spill src slot =>
    apply AdvanceTriple.of_effect
    · intro s ready loaded pre
      have step := spill_step p src slot pre.valid s ready loaded
        ⟨pre.rip, pre.writable, pre.apart⟩
      have len : (bytes (.spill src slot)).length =
          3 + (AddrMode.sib 4 none 0 slot).tail.length := by
        simp only [bytes, encodeMovM64R64, List.length_cons]
        omega
      have address : storeAddrAt p (.sib 4 none 0 slot)
          (3 + (AddrMode.sib 4 none 0 slot).tail.length) =
          (fun u => rspOf u + slot.value) := by
        funext u
        simp [storeAddrAt, AddrMode.addr, AddrMode.reg64]
      simpa only [effect, len, movM64R64Effect, address, readReg] using step
    · intro s pre
      apply Effect.avoids_of_mem (addr := rspOf s + slot.value) (len := 8) _ ?_ rfl
      · simp [effect, storeEffect, Effect.components, Component.isMem]
      · simpa [AddrMode.addr, AddrMode.reg64] using pre.apart
    · intro s _
      exact boundary_ne_program outside (inside _ (Nat.le_refl _))

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
