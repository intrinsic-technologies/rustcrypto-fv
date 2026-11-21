import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectSetup

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cf82
  readable : MemReadable s (stackPtr s+464) 4
  writable : ∀ k < 4, MemWritable s (stackPtr s+BitVec.ofNat 64 (368+8*k)) 8
  apart : ∀ k < 4, ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 (368+8*k)) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [72, 199, 132, 36, 136, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 128, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 120, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 112, 1, 0, 0, 0, 0, 0, 0, 68, 139, 164, 36, 208, 1, 0, 0, 72, 141, 172, 36, 80, 8, 0, 0, 72, 137, 239, 72, 141, 180, 36, 112, 1, 0, 0, 76, 137, 234, 68, 137, 225]

def effect (s : RamState) : Effect :=
  { rip := 0x10cfd3
    writes := [
      ⟨(.mem (stackPtr s+392) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+384) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+376) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+368) : Operand 64),0⟩,
      ⟨(.reg 12 : Operand 64), (memLoad s.external (stackPtr s+464) 32).setWidth 64⟩,
      ⟨(.reg 5 : Operand 64), stackPtr s+2128⟩,
      ⟨(.reg 7 : Operand 64),stackPtr s+2128⟩,
      ⟨(.reg 6 : Operand 64),stackPtr s+368⟩,
      ⟨(.reg 2 : Operand 64),(.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),(memLoad s.external (stackPtr s+464) 32).setWidth 64⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cf82 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10cf82 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip,hP.writable 3 (by decide),hP.apart 3 (by decide) 0xcf82 12 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 3 (by decide) 0xcf82 81 (by decide)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcf8e (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10cf8e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 384)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.apart 2 (by decide) 0xcf8e 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 2 (by decide) 0xcf82 81 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xcf9a (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10cf9a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 376)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.apart 1 (by decide) 0xcf9a 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 1 (by decide) 0xcf82 81 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xcfa6 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10cfa6 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 368)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.apart 0 (by decide) 0xcfa6 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0 (by decide) 0xcf82 81 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xcfb2 (by decide))
  advance_then (mov_r32_m32_effect_step 0x10cfb2 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d32 464)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm
      exact hP.readable
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xcfba (by decide))
  advance_then (lea_r64_effect_step 0x10cfba 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 2128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcfc2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cfc2 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcfc5 (by decide))
  advance_then (lea_r64_effect_step 0x10cfc5 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 368)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 67 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcfcd (by decide))
  advance_then (mov_r64_r64_effect_step 0x10cfcd 0x4c 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcfd0 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x10cfd0 0x44 0xe1 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cf82 bytes 78 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcfd3 (by decide))
  advance_finish [effect,stackPtr,Operand.read_reg64,State.regValue,modrmReg,modrmRm,gprNumber,rexR,rexB,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq]

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectSetup
