import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import P256.Proofs.Common.Instructions.And
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_local] P256.Proofs.Nonce.Update.Absorb.Prefix.TagHead.store_local

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a802
  remaining : (Operand.reg 15 : Operand 64).read s = 1
  writable : MemWritable s (rspOf s + 383) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 383) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x4c, 0x89, 0xf8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x21, 0xc8, 0x41, 0x83, 0xe7, 0x3f, 0x48, 0x1, 0xc6, 0x44, 0x88, 0xbc, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xfa]

def effect (s : RamState) : Effect :=
  { rip := 0x10a827
    writes := [⟨(.reg 0 : Operand 64),0⟩,⟨(.reg 1 : Operand 64),0x7fffffffffffffc0⟩,
      ⟨(.reg 15 : Operand 64),1⟩,⟨(.reg 6 : Operand 64),(Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 383) : Operand 8),1⟩,⟨(.reg 7 : Operand 64),(Operand.reg 12 : Operand 64).read s⟩,⟨(.reg 2 : Operand 64),1⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a802 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa802 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a802 bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x10a802 0 15) from mov_r64_r64_effect_step 0x10a802 0x4c 0xf8 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa805 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a805 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x10a802 bytes 3 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,movR64Imm64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa80f (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (andR64R64Effect 0x10a80f 0 1) from and_r64_r64_effect_step 0x10a80f 0x48 0xc8 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10a802 bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,Effect.forgetFlags,andR64R64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa812 (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (andR32Imm8Effect 0x10a812 4 15 63) from and_r32_imm8_rex_effect_step 0x10a812 0x41 0xe7 63 (by simp [RexNoWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10a802 bytes 16 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,Effect.forgetFlags,andR32Imm8Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa816 (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (addR64R64Effect 0x10a816 6 0) from add_r64_r64_effect_step 0x10a816 0x48 0xc6 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10a802 bytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,Effect.forgetFlags,addR64R64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa819 (by decide))⟩
  advance_then (mov_m8_r8_effect_step 0x10a819 0x44 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 383)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a802 bytes 23 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hP.writable
    · x86_norm; exact hP.codeApart 0xa819 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xa802 37 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa821 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10a821 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a802 bytes 31 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa824 (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a824 2 15) from mov_r64_r64_effect_step 0x10a824 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a802 bytes 34 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa827 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rem := hP.remaining
  simp only [BitVec.ofNat_eq_ofNat] at rem
  have rem32 : (Operand.reg 15#5 : Operand 32).read s = 1#32 := by
    change ((Operand.reg 15#5 : Operand 64).read s).setWidth 32 = _
    rw [rem]
    rfl
  apply hH.weaken
  · x86_norm [effect,rem,rem32,BitVec.add_zero]
  · x86_norm [effect,rem,rem32,BitVec.add_zero]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro,Or.inl,Or.inr,Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [effect,rem,rem32,BitVec.add_zero]

end P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderSetup
