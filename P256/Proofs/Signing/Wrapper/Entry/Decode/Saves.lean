import P256.Proofs.Signing.Wrapper.Entry.Decode.State
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def saveRegisterBytes : List UInt8 := [0x4d,0x89,0xc6,0x48,0x89,0xcb,0x49,0x89,0xf5]

def saveRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1023c9
    writes := [⟨(.reg 14 : Operand 64),s.regValue .r8⟩,
      ⟨(.reg 3 : Operand 64),s.regValue .rcx⟩,
      ⟨(.reg 13 : Operand 64),s.regValue .rsi⟩] }

theorem save_registers [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1023c0)
      (codeRange 0x1023c0 saveRegisterBytes) (Effect.post saveRegisterEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1023c0 0x4d 0xc6
    (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x23c3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1023c3 0x48 0xcb
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1023c0 saveRegisterBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23c6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1023c6 0x49 0xf5
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1023c0 saveRegisterBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23c9 (by decide))
  have reg0 : gprNumber (0#1) (rexR (UInt8.toBitVec 77)) (modrmReg 198) = 8#5 := by decide +kernel
  have reg1 : gprNumber (0#1) (rexR (UInt8.toBitVec 72)) (modrmReg 203) = 1#5 := by decide +kernel
  have reg2 : gprNumber (0#1) (rexR (UInt8.toBitVec 73)) (modrmReg 245) = 6#5 := by decide +kernel
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,saveRegisterEffect,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,saveRegisterEffect,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
    exact ⟨rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,saveRegisterEffect,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,saveRegisterEffect,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]


end P256.Proofs.Signing.Wrapper.Entry.Decode
