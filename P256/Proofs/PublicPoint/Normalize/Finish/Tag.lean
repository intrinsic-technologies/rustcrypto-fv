import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.PublicPoint.Normalize.Finish.Xor
import P256.Proofs.Common.Instructions.NegByte
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteLogic (andR8R8Effect and_r8_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)
open P256.Proofs.Common.Instructions.NegByte (negR8Effect neg_r8_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tag_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Program.ScalarFrame.FrameState s t 65 3352 1944)
    (tag : t.external[stackPtr s - 1616]? = some 0)
    (choice : (t.regValue .rbp).setWidth 8 = if select then 1 else 0) (rip : t.RIP = 0x10eae1) :
    ∃ u, Advances boundary 5 t u ∧ ReadyToStep u ∧ u.RIP = 0x10eaf3 ∧
      (Operand.reg 0 : Operand 8).read u = (if select then 0 else 1) ∧
      AgreesExcept [.reg 0, .reg 5, .flags, .rip] t u := by
  have code := programLoaded_codeIn state.loaded
  obtain ⟨t1, a1, r1, e1⟩ :=
    (neg_r8_effect_step 0x10eae1 0x40 0xdd (by simp [RexPrefix]) rfl rfl).advances
      (Program.readyToStep state.machine state.bindingsSupported)
      (programText_slice code 0xeae1 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeae4 (by decide)))
  change (negR8Effect 0x10eae1 5 t).Holds t t1 at e1
  have m1 : t1.external = t.external := e1.agrees.external (by simp [negR8Effect, Effect.components, Component.Covers])
  have sp1 : t1.regValue .rsp = stackPtr s - 1944 :=
    (e1.agrees.read (n := 64) (r := 4) (by simp [negR8Effect, Effect.components])).trans state.rsp
  have bp1 : (Operand.reg 5 : Operand 8).read t1 = (if select then 255 else 0) := by
    have h := e1.writes
    change (t1.regValue .rbp).setWidth 8 = (if select then 255 else 0)
    change t1.regValue .rbp = mergeGPR 8 _ _ at h
    rw [h, mergeGPR_low8]
    change -(t.regValue .rbp).setWidth 8 = (if select then 255 else 0)
    rw [choice]
    cases select <;> rfl
  have read1 : MemReadable t1 (t1.regValue .rsp + 328) 1 := by
    rw [sp1]
    have h := Program.readable_of_grow
      (Program.stack_sub_readable pre.stack (offset := 1616) (len := 1) (by decide) (by decide)) state.allocated
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h.of_external_eq m1
  obtain ⟨t2, a2, r2, e2⟩ :=
    (movzx_r32_m8_effect_step 0x10eae4 0 (.sib 4 none 0 (.d32 328))
      (by decide +kernel) rfl rfl).advances r1
      (programText_slice (code.of_external_eq m1) 0xeae4 _ (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, read1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeaec (by decide)))
  change (movzxR32M8Effect 0x10eae4 8 0 (.sib 4 none 0 (.d32 328)) t1).Holds t1 t2 at e2
  have m2 : t2.external = t.external :=
    (e2.agrees.external (by simp [Component.Covers])).trans m1
  have ax2 : (Operand.reg 0 : Operand 8).read t2 = 0 := by
    have h := e2.writes
    change (t2.regValue .rax).setWidth 8 = 0
    change t2.regValue .rax =
      (memLoad t1.external (t1.regValue .rsp + 328) 8).setWidth 64 at h
    rw [h, sp1, m1, memLoad_8, memByte]
    have addr : stackPtr s - 1944 + 328 = stackPtr s - 1616 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr]
    change (((t.external[stackPtr s - 1616]?).getD 0).toBitVec.setWidth 64).setWidth 8 = 0
    rw [tag]
    rfl
  obtain ⟨t3, a3, r3, e3⟩ := (xor_al_imm8_effect_step 0x10eaec 1).advances r2
    (programText_slice (code.of_external_eq m2) 0xeaec _ (by decide +kernel) (by decide +kernel))
    e2.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeaee (by decide)))
  have m3 : t3.external = t.external :=
    (e3.agrees.external (by simp [xorAlImm8Effect, Effect.components, Component.Covers])).trans m2
  have ax3 : (Operand.reg 0 : Operand 8).read t3 = 1 := by
    change ((Operand.reg 0 : Operand 64).read t3).setWidth 8 = _
    rw [show (Operand.reg 0 : Operand 64).read t3 = mergeGPR 8 _ _ from e3.writes,
      mergeGPR_low8, ax2]
    rfl
  have bp3 : (Operand.reg 5 : Operand 8).read t3 = (if select then 255 else 0) :=
    ((e2.agrees.trans e3.agrees).read (by simp [movzxR32M8Effect, xorAlImm8Effect, Effect.components])).trans bp1
  obtain ⟨t4, a4, r4, e4⟩ :=
    (and_r8_r8_rex_effect_step 0x10eaee 0x40 0xe8 (by simp [RexPrefix]) rfl).advances r3
      (programText_slice (code.of_external_eq m3) 0xeaee _ (by decide +kernel) (by decide +kernel))
      e3.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeaf1 (by decide)))
  change (andR8R8Effect 0x10eaee 0 5 t3).Holds t3 t4 at e4
  have m4 : t4.external = t.external :=
    (e4.agrees.external (by simp [andR8R8Effect, Effect.components, Component.Covers])).trans m3
  have ax4 : (Operand.reg 0 : Operand 8).read t4 = (if select then 1 else 0) := by
    change ((Operand.reg 0 : Operand 64).read t4).setWidth 8 = _
    rw [show (Operand.reg 0 : Operand 64).read t4 = mergeGPR 8 _ _ from e4.writes,
      mergeGPR_low8, ax3, bp3]
    cases select <;> rfl
  obtain ⟨u, a5, r5, e5⟩ := (xor_al_imm8_effect_step 0x10eaf1 1).advances r4
    (programText_slice (code.of_external_eq m4) 0xeaf1 _ (by decide +kernel) (by decide +kernel))
    e4.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeaf3 (by decide)))
  refine ⟨u, (((a1.trans a2).trans a3).trans a4).trans a5, r5, e5.rip, ?_, ?_⟩
  · change ((Operand.reg 0 : Operand 64).read u).setWidth 8 = _
    rw [show (Operand.reg 0 : Operand 64).read u = mergeGPR 8 _ _ from e5.writes,
      mergeGPR_low8, ax4]
    cases select <;> rfl
  · exact ((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).mono
      (by simp [negR8Effect, movzxR32M8Effect, xorAlImm8Effect, andR8R8Effect, Effect.components])

end P256.Proofs.PublicPoint.Normalize.Finish
