import Md5.Proofs.Buffered.Update.Counter
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Ranges

import Md5.Proofs.Buffered.Update.ResetSecond.Layout

namespace Md5.Proofs.Buffered.ResetSecond
open X86 X86.Machine X86.UserProcess X86Proofs Block

def incrementPrepareBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then
    [0x48, 0xff, 0x44, 0x24, 0x70, 0xba, 0x01, 0x00, 0x00, 0x00,
      0x48, 0x8d, 0x7c, 0x24, 0x60, 0x48, 0x8d, 0x74, 0x24, 0x20]
  else
    [0x48, 0xff, 0x44, 0x24, 0x58, 0xba, 0x01, 0x00, 0x00, 0x00,
      0x48, 0x8d, 0x7c, 0x24, 0x48, 0x48, 0x89, 0xde]

def incrementPrepareEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x100a1f
    writes := [⟨(.mem (kind.context s + 80) : Operand 64),
      (.mem (kind.context s + 80) : Operand 64).read s + 1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), kind.context s + 64⟩,
      ⟨(.reg 6 : Operand 64), if kind = .resetDiscardSecond then kind.context s
        else (.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem increment_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (boundary : ReturnBoundary) (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary
      (Memory.StorePre (pc kind 0x100a0d) (if kind = .resetDiscardSecond then 20 else 18)
        (fun s ↦ kind.context s + 80) 8)
      (codeRange (pc kind 0x100a0d) (incrementPrepareBytes kind))
      (incrementPrepareEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  · simp only [incrementPrepareBytes, reduceCtorEq, ite_false]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.inc_m64_effect_step 0x100a0d 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.incM64Effect 0x100a0d
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa12 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x100a12 0xba (by decide) 1
    case sub => exact codeRange_mem_of_drop (p := 0x100a0d) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa17 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x100a17 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a0d) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa1c (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100a1c 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a0d) 15 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa1f (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      rfl
  · simp only [incrementPrepareBytes, reduceCtorEq, ite_false]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.inc_m64_effect_step 0x10109d 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.incM64Effect 0x10109d
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10a2 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x1010a2 0xba (by decide) 1
    case sub => exact codeRange_mem_of_drop (p := 0x10109d) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10a7 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x1010a7 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10109d) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10ac (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1010ac 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10109d) 15 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10af (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      rfl
  · simp only [incrementPrepareBytes, ite_true]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.inc_m64_effect_step 0x101579 0x48
      (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 112) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.incM64Effect 0x101579
          (.sib 4 none 0 (.d8 112)) s).components =
          [.mem (stackPtr s + 112) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x157e (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x10157e 0xba (by decide) 1
    case sub => exact codeRange_mem_of_drop (p := 0x101579) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1583 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x101583 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101579) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1588 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x101588 0x48 (by unfold RexWPrefix; decide)
      6 (.sib 4 none 0 (.d8 32)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101579) 15 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x158d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    · x86_norm [incrementPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, stackPtr]
      rfl

def addPrepareBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then
    [0x48, 0x01, 0x54, 0x24, 0x70, 0x48, 0x8d, 0x7c, 0x24, 0x60, 0x48, 0x89, 0xde]
  else
    [0x48, 0x01, 0x54, 0x24, 0x58, 0x48, 0x8d, 0x7c, 0x24, 0x48, 0x49, 0x89, 0xf4]

def addPrepareEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x100a42
    writes := [⟨(.mem (kind.context s + 80) : Operand 64),
      (.mem (kind.context s + 80) : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), kind.context s + 64⟩,
      ⟨(.reg (if kind = .resetDiscardSecond then 6 else 12) : Operand 64),
        (.reg kind.inputRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem add_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (boundary : ReturnBoundary) (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary
      (Memory.StorePre (pc kind 0x100a35) 13 (fun s ↦ kind.context s + 80) 8)
      (codeRange (pc kind 0x100a35) (addPrepareBytes kind)) (addPrepareEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  · simp only [addPrepareBytes, reduceCtorEq, ite_false]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.add_m64_r64_effect_step 0x100a35 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.addM64R64Effect 0x100a35
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa3a (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x100a3a 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a35) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa3f (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100a3f 0x49 0xf4
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a35) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa42 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      rfl
  · simp only [addPrepareBytes, reduceCtorEq, ite_false]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.add_m64_r64_effect_step 0x1010c5 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 88))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 88) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.addM64R64Effect 0x1010c5
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 88)) s).components =
          [.mem (stackPtr s + 88) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10ca (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x1010ca 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1010c5) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10cf (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1010cf 0x49 0xf4
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1010c5) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10d2 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      rfl
  · simp only [addPrepareBytes, ite_true]
    dsimp only [pc, UpdateKind.context, UpdateKind.contextOffset]
    simp only [BitVec.add_assoc]
    md5_run_begin Update.Counter.add_m64_r64_effect_step 0x1015a3 0x48
      (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d8 112))
      (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_, ?_⟩
      · x86_norm
        exact hP.write
      · x86_norm
        exact MemoryRoutines.rangeApart_slice_right hP.code 0 5 (by decide)
    case av =>
      intro s hP
      apply Effect.avoids_of_mem (addr := stackPtr s + 112) (len := 8) ?_ hP.code rfl
      intro c hc hm
      have hcomponents : (Update.Counter.addM64R64Effect 0x1015a3
          (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) 2)
          (.sib 4 none 0 (.d8 112)) s).components =
          [.mem (stackPtr s + 112) 8, .flags, .rip] := by
        x86_norm [stackPtr]
        rfl
      rw [hcomponents] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rfl
      · exact Bool.noConfusion hm
      · exact Bool.noConfusion hm
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15a8 (by decide +kernel)
    md5_run_then lea_r64_effect_step 0x1015a8 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1015a3) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15ad (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1015ad 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1015a3) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15b0 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc]
    · x86_norm [addPrepareEffect, pc, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, BitVec.add_assoc, stackPtr]
      rfl

def positionClearBytes (kind : UpdateKind) : List UInt8 :=
  [0xc6, 0x44, 0x24, UInt8.ofNat (kind.contextOffset + 63), 0x00]

def positionClearEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x100a29
    writes := [⟨(.mem (kind.context s + 63) : Operand 8), 0⟩] }

theorem position_clear [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary
      (Memory.StorePre (pc kind 0x100a24) 5 (fun s ↦ kind.context s + 63) 1)
      (codeRange (pc kind 0x100a24) (positionClearBytes kind))
      (positionClearEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  all_goals unfold positionClearEffect
  all_goals dsimp only [UpdateKind.context, UpdateKind.contextOffset]
  all_goals simp only [BitVec.add_assoc]
  · apply AdvancesBlock.first
      (Stores.mov_m8_imm8_effect_step 0x100a24 (.sib 4 none 0 (.d8 71))
        (by decide) (by decide) (by decide) 0)
    · exact fun _ h ↦ h
    · exact fun _ h ↦ h
    · intro s hP
      exact Memory.storeEffect_avoids (by rfl) (fun s ↦ stackPtr s + 71)
        (fun _ ↦ (0 : BitVec 8)) hP
    · intro _ _
      exact text_address_ne_return hOutside 0xa29 (by decide +kernel)
  · apply AdvancesBlock.first
      (Stores.mov_m8_imm8_effect_step 0x1010b4 (.sib 4 none 0 (.d8 71))
        (by decide) (by decide) (by decide) 0)
    · exact fun _ h ↦ h
    · exact fun _ h ↦ h
    · intro s hP
      exact Memory.storeEffect_avoids (by rfl) (fun s ↦ stackPtr s + 71)
        (fun _ ↦ (0 : BitVec 8)) hP
    · intro _ _
      exact text_address_ne_return hOutside 0x10b9 (by decide +kernel)
  · apply AdvancesBlock.first
      (Stores.mov_m8_imm8_effect_step 0x101592 (.sib 4 none 0 (.d8 95))
        (by decide) (by decide) (by decide) 0)
    · exact fun _ h ↦ h
    · exact fun _ h ↦ h
    · intro s hP
      exact Memory.storeEffect_avoids (by rfl) (fun s ↦ stackPtr s + 95)
        (fun _ ↦ (0 : BitVec 8)) hP
    · intro _ _
      exact text_address_ne_return hOutside 0x1597 (by decide +kernel)

def sourceRestoreBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then [] else [0x4c, 0x89, 0xe6]

def sourceRestoreEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := pc kind 0x100a4a
    writes := [⟨(.reg kind.inputRegister : Operand 64),
      (.reg (batchSavedInputRegister kind) : Operand 64).read s⟩] }

theorem source_restore [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (boundary : ReturnBoundary) (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x100a47)
      (codeRange (pc kind 0x100a47) (sourceRestoreBytes kind))
      (sourceRestoreEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  · simp only [sourceRestoreBytes, reduceCtorEq, ite_false]
    md5_run_begin mov_r64_r64_effect_step 0x100a47 0x4c 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa4a (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
  · simp only [sourceRestoreBytes, reduceCtorEq, ite_false]
    md5_run_begin mov_r64_r64_effect_step 0x1010d7 0x4c 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10da (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
    · x86_norm [sourceRestoreEffect, pc, UpdateKind.inputRegister, batchSavedInputRegister]
  · intro s hs hc hp
    refine ⟨0, s, by simp, hs, hc, ?_⟩
    refine ⟨hp, ?_, by trivial, AgreesExcept.refl _ _⟩
    rfl

end Md5.Proofs.Buffered.ResetSecond
