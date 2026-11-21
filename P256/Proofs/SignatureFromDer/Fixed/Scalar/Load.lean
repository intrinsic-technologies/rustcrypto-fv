import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fab7
  readable : ∀ off ∈ ([40,48,56,64] : List (BitVec 64)), MemReadable s (stackPtr s + off) 8

def loadBytesCode : List UInt8 :=
  [0x4c,0x8b,0x7c,0x24,0x28,0x4c,0x8b,0x64,0x24,0x30,0x4c,0x8b,0x6c,0x24,0x38,0x48,0x8b,0x6c,0x24,0x40]

def loadEffect (s : RamState) : Effect :=
  { rip := 0x10facb
    writes := [⟨(.reg 15 : Operand 64), (Operand.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.reg 12 : Operand 64), (Operand.mem (stackPtr s + 48) : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), (Operand.mem (stackPtr s + 56) : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64), (Operand.mem (stackPtr s + 64) : Operand 64).read s⟩] }

theorem scalar_load [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x10fab7 loadBytesCode) (Effect.post loadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fab7 0x4c (by simp [RexWPrefix])
    7 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 40 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfabc (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fabc 0x4c (by simp [RexWPrefix])
    4 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fab7 loadBytesCode 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfac1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fac1 0x4c (by simp [RexWPrefix])
    5 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fab7 loadBytesCode 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfac6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fac6 0x48 (by simp [RexWPrefix])
    5 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fab7 loadBytesCode 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 64 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfacb (by decide))
  advance_finish [loadEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.SignatureFromDer.Fixed.Scalar
