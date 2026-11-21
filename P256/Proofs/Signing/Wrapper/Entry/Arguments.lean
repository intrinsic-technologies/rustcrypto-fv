import P256.Spec
import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure LoadArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1023a1
  pointer : MemReadable s (s.regValue .rdi) 8
  length : MemReadable s (s.regValue .rdx) 8

def loadArgumentsBytes : List UInt8 :=
  [0x49,0x89,0xd7,0x49,0x89,0xfc,0x48,0x8b,0x7,0x48,0x8b,0x2a]

def loadArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x1023ad
    writes := [⟨(.reg 15 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 12 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (s.regValue .rdi) 64⟩,
      ⟨(.reg 5 : Operand 64), memLoad s.external (s.regValue .rdx) 64⟩] }

theorem load_arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadArgumentsPre (codeRange 0x1023a1 loadArgumentsBytes)
      (Effect.post loadArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1023a1 0x49 0xd7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x23a4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1023a4 0x49 0xfc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1023a1 loadArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x23a7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1023a7 0x48 (by simp [RexWPrefix])
    0 (.base 7 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023a1 loadArgumentsBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdi + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdi))).mpr hP.pointer
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x23aa (by decide))
  advance_then (mov_r64_m64_effect_step 0x1023aa 0x48 (by simp [RexWPrefix])
    5 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023a1 loadArgumentsBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdx + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdx))).mpr hP.length
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x23ad (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, modrmReg, modrmRm]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdi)).symm
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdx)).symm
  · intro i
    cases i <;> x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, gprNumber, rexR, rexB, modrmRm, modrmReg]

end P256.Proofs.Signing.Wrapper.Entry
