import Md5.Proofs.Buffered.FinalizeReset.Prepare.Model
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Finalize.Store8
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

structure TailPre (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = (variant.address 0x1007cd)
  position : ((.reg 15 : Operand 64).read s).toNat < 64

def tailBodyEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  let pos := (.reg 15 : Operand 64).read s
  { rip := (variant.address 0x1007e0)
    writes := [⟨(.mem (stackPtr s + pos + 8) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + 9⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def tailBytes : List UInt8 :=
  [0x42, 0xc6, 0x44, 0x3c, 0x08, 0x80, 0x4a, 0x8d, 0x3c, 0x3c,
    0x48, 0x83, 0xc7, 0x09, 0x31, 0xf6, 0x48, 0x89, 0xda]

theorem marker_writable {variant : Variant} {s : RamState} (hs : Storage s variant)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) :
    Memory.MemWritable s (stackPtr s + (.reg 15 : Operand 64).read s + 8) 1 := by
  have hsize := variant.stackBytes_bounds
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
    Export.stackWritable hs (((.reg 15 : Operand 64).read s).toNat + 8) 1 (by omega)

theorem marker_apart {variant : Variant} {s : RamState} (hs : Storage s variant)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) (offset len : Nat)
    (hc : offset + len ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + (.reg 15 : Operand 64).read s + 8) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  have hsize := variant.stackBytes_bounds
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using Export.stackTextApart hs
      (((.reg 15 : Operand 64).read s).toNat + 8) 1 offset len (by omega) hc

theorem tail_body_execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ TailPre s variant) (codeRange (variant.address 0x1007cd) tailBytes) (fun s ↦ tailBodyEffect s variant) := by
  cases variant with
  | saved =>
    unfold tailBytes
    md5_run_begin (Finalize.mov_m8_imm8_rex_effect_step 0x1007cd 0x42
      (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 8))
      (by decide) (by decide) (by decide) 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm [Variant.address, BitVec.shiftLeft_zero]
        simpa [stackPtr, Operand.read, BitVec.add_assoc] using marker_writable h.toStorage h.position
      · x86_norm [Variant.address, BitVec.shiftLeft_zero]
        simpa [stackPtr, Operand.read, BitVec.add_assoc, Extracted.textAddress] using marker_apart h.toStorage h.position 0x7cd 6 (by decide +kernel)
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip (show
        (Finalize.movM8Imm8RexEffect 0x1007cd (.sib 4 (some 15) 0 (.d8 8)) 128 s).components =
          [.mem (stackPtr s + (.reg 15 : Operand 64).read s + 8) 1, .rip] by x86_norm [Variant.address, BitVec.shiftLeft_zero, stackPtr]; rfl)
      exact marker_apart h.toStorage h.position 0x7cd 19 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7d3 (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x1007d3 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007cd) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7d7 (by decide +kernel)
    md5_run_then (add_r64_imm8_effect_step 0x1007d7 0x48 0xc7 9
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007cd) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7db (by decide +kernel)
    md5_run_then (xor_r32_r32_effect_step 0x1007db 0xf6 (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007cd) 14 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7dd (by decide +kernel)
    md5_run_then (mov_r64_r64_effect_step 0x1007dd 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007cd) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7e0 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, tailBodyEffect]
    · x86_norm [Variant.address, tailBodyEffect, stackPtr, BitVec.shiftLeft_zero]
      simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
    · intro i; cases i <;> x86_norm [Variant.address, tailBodyEffect]
    · x86_norm [Variant.address, tailBodyEffect, stackPtr, BitVec.shiftLeft_zero]
      rfl
  | direct =>
    unfold tailBytes
    md5_run_begin (Finalize.mov_m8_imm8_rex_effect_step 0x100e7d 0x42
      (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 8))
      (by decide) (by decide) (by decide) 128)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · x86_norm [Variant.address, BitVec.shiftLeft_zero]
        simpa [stackPtr, Operand.read, BitVec.add_assoc] using marker_writable h.toStorage h.position
      · x86_norm [Variant.address, BitVec.shiftLeft_zero]
        simpa [stackPtr, Operand.read, BitVec.add_assoc, Extracted.textAddress] using marker_apart h.toStorage h.position 0xe7d 6 (by decide +kernel)
    case av =>
      intro s h
      apply Effect.avoids_of_components_mem_rip (show
        (Finalize.movM8Imm8RexEffect 0x100e7d (.sib 4 (some 15) 0 (.d8 8)) 128 s).components =
          [.mem (stackPtr s + (.reg 15 : Operand 64).read s + 8) 1, .rip] by x86_norm [Variant.address, BitVec.shiftLeft_zero, stackPtr]; rfl)
      exact marker_apart h.toStorage h.position 0xe7d 19 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe83 (by decide +kernel)
    md5_run_then (lea_r64_effect_step 0x100e83 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e7d) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe87 (by decide +kernel)
    md5_run_then (add_r64_imm8_effect_step 0x100e87 0x48 0xc7 9
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e7d) 10 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe8b (by decide +kernel)
    md5_run_then (xor_r32_r32_effect_step 0x100e8b 0xf6 (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e7d) 14 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe8d (by decide +kernel)
    md5_run_then (mov_r64_r64_effect_step 0x100e8d 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e7d) 16 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe90 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, tailBodyEffect]
    · x86_norm [Variant.address, tailBodyEffect, stackPtr, BitVec.shiftLeft_zero]
      simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
    · intro i; cases i <;> x86_norm [Variant.address, tailBodyEffect]
    · x86_norm [Variant.address, tailBodyEffect, stackPtr, BitVec.shiftLeft_zero]
      rfl

end Md5.Proofs.Buffered.FinalizeReset.Prepare
