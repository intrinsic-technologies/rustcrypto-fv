import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def setupBytes : List UInt8 :=
  [0x48,0x8d,0x74,0x24,0x8,0x48,0x8d,0x84,0x24,0x88,0,0,0,
    0xb9,9,0,0,0,0x48,0x89,0xc7]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x101860
    writes := [⟨(.reg 6 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 0 : Operand 64), stackPtr s + 136⟩,
      ⟨(.reg 1 : Operand 64), 9⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 136⟩] }

theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10184b) (codeRange 0x10184b setupBytes)
      (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10184b 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x1850 (by decide))
  advance_then (lea_r64_effect_step 0x101850 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10184b setupBytes 5 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1858 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x101858 0xb9 (by decide) 9)
  case sub => exact codeRange_slice_subset 0x10184b setupBytes 13 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x185d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10185d 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10184b setupBytes 18 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1860 (by decide))⟩
  advance_finish [setupEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, modrmRm, modrmReg, opcodeReg,
    UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat, BitVec.xor_self]

def serializerSetupBytes : List UInt8 := [0x48,0x89,0xe7,0x48,0x89,0xc6,0x31,0xd2]

def serializerSetupEffect (s : RamState) : Effect :=
  { rip := 0x10186b
    flags := some (xorFlags (0 : BitVec 32))
    writes := [⟨(.reg 7 : Operand 64), stackPtr s⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rax⟩,
      ⟨(.reg 2 : Operand 64), 0⟩] }

theorem serializer_setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x101863) (codeRange 0x101863 serializerSetupBytes)
      (Effect.post serializerSetupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x101863 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x1866 (by decide))
  advance_then (mov_r64_r64_effect_step 0x101866 0x48 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101863 serializerSetupBytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1869 (by decide))⟩
  advance_then (xor_r32_r32_effect_step 0x101869 0xd2 (by decide))
  case sub => exact codeRange_slice_subset 0x101863 serializerSetupBytes 6 2
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x186b (by decide))⟩
  advance_finish [serializerSetupEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, modrmRm, modrmReg, opcodeReg,
    UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat, BitVec.xor_self]

end P256.Proofs.Sec1.Wrapper.Success
