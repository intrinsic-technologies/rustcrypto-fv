import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Finish.HashSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a867
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemWritable s (stackPtr s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x4, 0x24, 0x0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xe6, 0x48, 0x89, 0xdf]

def effect (s : RamState) : Effect :=
  { rip := 0x10a890
    writes := [
      ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), 0⟩] }

set_option maxHeartbeats 800000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a867 bytes)
      (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10a867 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 24 (by simp), hP.codeApart 24 (by simp) 0xa867 9 (by decide)⟩
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0xa870 (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 24 (by simp) 0xa867 41 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10a870 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a867 bytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0xa870 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0xa867 41 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa879 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a879 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a867 bytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0xa879 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0xa867 41 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa882 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a882 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a867 bytes 27 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0xa882 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0xa867 41 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa88a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10a88a 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a867 bytes 35 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa88d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10a88d 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a867 bytes 38 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa890 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Seeded.Finish.HashSetup
