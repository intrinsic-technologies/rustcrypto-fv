import P256.Proofs.Nonce.Update.Absorb.Memory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.ShiftLeft.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
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
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Common.Instructions.ShiftLeft

attribute [local x86_compose] shlR64Effect shlFlags

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a261
  writable : ∀ off ∈ ([80,424] : List (BitVec 64)), MemWritable s (rspOf s + off) 8
  codeApart : ∀ off ∈ ([80,424] : List (BitVec 64)), ∀ pc len : Nat,
    pc + len ≤ 118431 → RangeApart (rspOf s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x4c, 0x89, 0xe8, 0x48, 0xc1, 0xe0, 0x4, 0x48, 0x1, 0xe8, 0x48, 0x89, 0x44, 0x24, 0x50, 0x4c, 0x89, 0xac, 0x24, 0xa8, 0x1, 0x0, 0x0, 0x4d, 0x85, 0xed]

def effect (s : RamState) : Effect :=
  { rip := 0x10a27b
    writes := [⟨(.reg 0 : Operand 64),
      ((Operand.reg 13 : Operand 64).read s <<< 4) + (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 80) : Operand 64),
        ((Operand.reg 13 : Operand 64).read s <<< 4) + (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 424) : Operand 64),(Operand.reg 13 : Operand 64).read s⟩]
    flags := some (testFlags ((Operand.reg 13 : Operand 64).read s)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a261 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa261 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a261 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10a261 0x4c 0xe8 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa264 (by decide))
  advance_then (show StepEffect _ _ (shlR64Effect 0x10a264 4 0 4) from shl_r64_imm8_effect_step 0x10a264 0x48 0xe0 4 (by simp [RexWPrefix]) rfl rfl)
  case loc => exact shlR64Effect_local _ _ _ 4 (by decide)
  case sub => exact codeRange_slice_subset 0x10a261 bytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, shlR64Effect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa268 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10a268 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a261 bytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa26b (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10a26b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a261 bytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 (by simp)
    · x86_norm
      exact hP.codeApart 80 (by simp) 0xa26b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 80 (by simp) 0xa261 26 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa270 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a270 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a261 bytes 15 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 424 (by simp)
    · x86_norm
      exact hP.codeApart 424 (by simp) 0xa270 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 424 (by simp) 0xa261 26 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa278 (by decide))
  advance_then (show StepEffect _ _ (testR64R64Effect 0x10a278 13 13) from test_r64_r64_effect_step 0x10a278 0x4d 0xed (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a261 bytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa27b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect, BitVec.and_self, testFlags]
  · x86_norm [effect]

end P256.Proofs.Nonce.Update.Absorb.Setup
