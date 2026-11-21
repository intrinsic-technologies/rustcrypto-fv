import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.Buffered.Update.ResetSecond.Layout
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.ResetSecond

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then [0x48, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x20, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xea] else
  [0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08, 0x4c, 0x89, 0xe2]

def shortCopyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x1009ab)
    writes := (if kind = .resetDiscardSecond then [⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩] else []) ++ [⟨(.reg 7 : Operand 64), stackPtr s + (.reg (positionRegister kind) : Operand 64).read s + BitVec.ofNat 64 kind.contextOffset⟩,
      ⟨(.reg 2 : Operand 64), (.reg (savedInputRegister kind) : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem short_copy_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x1009a0))
      (codeRange (pc kind 0x1009a0) (shortCopyBytes kind)) (shortCopyEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    simp only [shortCopyBytes, show UpdateKind.resetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin lea_r64_effect_step (pc UpdateKind.resetSecond 0x1009a0) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x1009a4).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc UpdateKind.resetSecond 0x1009a4) 0x48 0xc7 8
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x1009a0)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x1009a8).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc UpdateKind.resetSecond 0x1009a8) 0x4c 0xe2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x1009a0)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x1009ab).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [shortCopyBytes, show UpdateKind.finalizeResetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin lea_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x1009a0) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x1009a4).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc UpdateKind.finalizeResetSecond 0x1009a4) 0x48 0xc7 8
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x1009a0)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x1009a8).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x1009a8) 0x4c 0xe2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x1009a0)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x1009ab).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [shortCopyBytes, ite_true]
    md5_run_begin lea_r64_effect_step (pc .resetDiscardSecond 0x1009a0) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 5) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x1009a4).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc .resetDiscardSecond 0x1009a4) 0x48 0xc7 32
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009a0)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x101518).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101518 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009a0)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x10151b).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc .resetDiscardSecond 0x1009a8) 0x4c 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009a0)) 11 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x1009ab).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [shortCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]


def fillCopyBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then [0x4c, 0x8d, 0x2c, 0x13, 0x48, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x20, 0x48, 0x89, 0xde] else
  [0x4c, 0x8d, 0x24, 0x16, 0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08]

def fillCopyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x100a0a)
    writes := (if kind = .resetDiscardSecond then [⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩] else []) ++ [⟨(.reg (savedInputRegister kind) : Operand 64), (.reg kind.inputRegister : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg (positionRegister kind) : Operand 64).read s + BitVec.ofNat 64 kind.contextOffset⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem fill_copy_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x1009fe))
      (codeRange (pc kind 0x1009fe) (fillCopyBytes kind)) (fillCopyEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    simp only [fillCopyBytes, show UpdateKind.resetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin lea_r64_effect_step (pc UpdateKind.resetSecond 0x1009fe) 0x4c (by unfold RexWPrefix; decide)
      4 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a02).toNat - 0x100000) (by decide +kernel)
    md5_run_then lea_r64_effect_step (pc UpdateKind.resetSecond 0x100a02) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x1009fe)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a06).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc UpdateKind.resetSecond 0x100a06) 0x48 0xc7 8
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x1009fe)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a0a).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [fillCopyBytes, show UpdateKind.finalizeResetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin lea_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x1009fe) 0x4c (by unfold RexWPrefix; decide)
      4 (.sib 6 (some 2) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a02).toNat - 0x100000) (by decide +kernel)
    md5_run_then lea_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a02) 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x1009fe)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a06).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc UpdateKind.finalizeResetSecond 0x100a06) 0x48 0xc7 8
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x1009fe)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a0a).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read]
    · intro i; cases i <;> x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [fillCopyBytes, ite_true]
    md5_run_begin lea_r64_effect_step (pc .resetDiscardSecond 0x1009fe) 0x4c (by unfold RexWPrefix; decide)
      5 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a02).toNat - 0x100000) (by decide +kernel)
    md5_run_then lea_r64_effect_step (pc .resetDiscardSecond 0x100a02) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 5) 0 .none) (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009fe)) 4 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a06).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_imm8_effect_step (pc .resetDiscardSecond 0x100a06) 0x48 0xc7 32
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009fe)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x101573).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101573 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x1009fe)) 12 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x101576).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [fillCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]


def tailPointerBytes (kind : UpdateKind) : List UInt8 :=
  [0x4c, 0x89, 0xf0, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    0x48, 0x21, 0xc8, 0x41, 0x83, 0xe6, 0x3f, 0x48, 0x01, (if kind = .resetDiscardSecond then 0xc3 else 0xc6)]

def tailPointerEffect (kind : UpdateKind) (s : RamState) : Effect :=
  let full := (.reg 14 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := (pc kind 0x100a61)
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 14 : Operand 64), (((.reg 14 : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


set_option maxHeartbeats 400000 in
theorem tail_pointer_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a4a))
      (codeRange (pc kind 0x100a4a) (tailPointerBytes kind)) (tailPointerEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    simp only [tailPointerBytes, show UpdateKind.resetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin mov_r64_r64_effect_step (pc UpdateKind.resetSecond 0x100a4a) 0x4c 0xf0
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a4d).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_imm64_effect_step (pc UpdateKind.resetSecond 0x100a4d) 0x48 0xb9
      (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x100a4a)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a57).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r64_r64_effect_step (pc UpdateKind.resetSecond 0x100a57) 0x48 0xc8
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x100a4a)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a5a).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r32_imm8_rex_effect_step (pc UpdateKind.resetSecond 0x100a5a) 0x41 0xe6 63
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x100a4a)) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a5e).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_r64_effect_step (pc UpdateKind.resetSecond 0x100a5e) 0x48 0xc6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x100a4a)) 20 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a61).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
    · intro i; cases i <;> x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [tailPointerBytes, show UpdateKind.finalizeResetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin mov_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a4a) 0x4c 0xf0
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a4d).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_imm64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a4d) 0x48 0xb9
      (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x100a4a)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a57).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a57) 0x48 0xc8
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x100a4a)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a5a).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r32_imm8_rex_effect_step (pc UpdateKind.finalizeResetSecond 0x100a5a) 0x41 0xe6 63
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x100a4a)) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a5e).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a5e) 0x48 0xc6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x100a4a)) 20 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a61).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
    · intro i; cases i <;> x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [tailPointerBytes, ite_true]
    md5_run_begin mov_r64_r64_effect_step (pc .resetDiscardSecond 0x100a4a) 0x4c 0xf0
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a4d).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_imm64_effect_step (pc .resetDiscardSecond 0x100a4d) 0x48 0xb9
      (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a4a)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a57).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r64_r64_effect_step (pc .resetDiscardSecond 0x100a57) 0x48 0xc8
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a4a)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a5a).toNat - 0x100000) (by decide +kernel)
    md5_run_then and_r32_imm8_rex_effect_step (pc .resetDiscardSecond 0x100a5a) 0x41 0xe6 63
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a4a)) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a5e).toNat - 0x100000) (by decide +kernel)
    md5_run_then add_r64_r64_effect_step (pc .resetDiscardSecond 0x100a5e) 0x48 0xc3
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a4a)) 20 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a61).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
    · intro i; cases i <;> x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailPointerEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]


def tailCopyBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then [0x48, 0x8d, 0x7c, 0x24, 0x20, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xf2] else
  [0x48, 0x89, 0xdf, 0x4c, 0x89, 0xf2]

def tailCopyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x100a6c)
    writes := (if kind = .resetDiscardSecond then [⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩] else []) ++ [⟨(.reg 7 : Operand 64), if kind = .resetDiscardSecond then kind.context s else (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩] }


theorem tail_copy_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a66))
      (codeRange (pc kind 0x100a66) (tailCopyBytes kind)) (tailCopyEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    simp only [tailCopyBytes, show UpdateKind.resetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin mov_r64_r64_effect_step (pc UpdateKind.resetSecond 0x100a66) 0x48 0xdf
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a69).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc UpdateKind.resetSecond 0x100a69) 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.resetSecond 0x100a66)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.resetSecond 0x100a6c).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [tailCopyBytes, show UpdateKind.finalizeResetSecond = .resetDiscardSecond ↔ False by decide, ite_false]
    md5_run_begin mov_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a66) 0x48 0xdf
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a69).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc UpdateKind.finalizeResetSecond 0x100a69) 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc UpdateKind.finalizeResetSecond 0x100a66)) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc UpdateKind.finalizeResetSecond 0x100a6c).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
  ·
    simp only [tailCopyBytes, ite_true]
    md5_run_begin lea_r64_effect_step (pc .resetDiscardSecond 0x100a66) 0x48 (by unfold RexWPrefix; decide)
      7 (.sib 4 none 0 (.d8 32)) (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x1015d6).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1015d6 0x48 0xde
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a66)) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a69).toNat - 0x100000) (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step (pc .resetDiscardSecond 0x100a69) 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (pc .resetDiscardSecond 0x100a66)) 8 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside ((pc .resetDiscardSecond 0x100a6c).toNat - 0x100000) (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]
    · x86_norm [tailCopyEffect, pc, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.context, UpdateKind.inputRegister, stackPtr]

end Md5.Proofs.Buffered.ResetSecond
