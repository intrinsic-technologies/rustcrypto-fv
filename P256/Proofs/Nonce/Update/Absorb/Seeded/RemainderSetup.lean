import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import P256.Proofs.Common.Instructions.And
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_local] Prefix.TagHead.store_local

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a34c
  remaining : (Operand.reg 3 : Operand 64).read s = 1
  writable : MemWritable s (rspOf s + 215) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 215) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x48, 0x89, 0xd8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x21, 0xc8, 0x83, 0xe3, 0x3f, 0x49, 0x1, 0xc4, 0x88, 0x9c, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0x98, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xda]

def effect (s : RamState) : Effect :=
  { rip := 0x10a377
    writes := [⟨(.reg 0 : Operand 64),0⟩,⟨(.reg 1 : Operand 64),0x7fffffffffffffc0⟩,
      ⟨(.reg 3 : Operand 64),1⟩,⟨(.reg 12 : Operand 64),(Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 215) : Operand 8),1⟩,⟨(.reg 7 : Operand 64),rspOf s + 152⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 12 : Operand 64).read s⟩,⟨(.reg 2 : Operand 64),1⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a34c bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa34c bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a34c bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x10a34c 0 3) from mov_r64_r64_effect_step 0x10a34c 0x48 0xd8 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa34f (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10a34f 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x10a34c bytes 3 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,movR64Imm64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa359 (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (andR64R64Effect 0x10a359 0 1) from and_r64_r64_effect_step 0x10a359 0x48 0xc8 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10a34c bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,P256.Proofs.Common.Instructions.Effect.forgetFlags,andR64R64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa35c (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (andR32Imm8Effect 0x10a35c 3 3 63) from and_r32_imm8_effect_step 0x10a35c 0xe3 63 rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10a34c bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,P256.Proofs.Common.Instructions.Effect.forgetFlags,andR32Imm8Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa35f (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (addR64R64Effect 0x10a35f 12 0) from add_r64_r64_effect_step 0x10a35f 0x49 0xc4 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10a34c bytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers,P256.Proofs.Common.Instructions.Effect.forgetFlags,addR64R64Effect,Effect.components,Write.component,Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa362 (by decide))⟩
  advance_then (mov_m8_r8_legacy_effect_step 0x10a362 3 (by decide) (.sib 4 none 0 (.d32 215)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a34c bytes 22 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hP.writable
    · x86_norm; exact hP.codeApart 0xa362 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xa34c 43 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa369 (by decide))
  advance_then (lea_r64_effect_step 0x10a369 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a34c bytes 29 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa371 (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a371 6 12) from mov_r64_r64_effect_step 0x10a371 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a34c bytes 37 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa374 (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a374 2 3) from mov_r64_r64_effect_step 0x10a374 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a34c bytes 40 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa377 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rem := hP.remaining
  simp only [BitVec.ofNat_eq_ofNat] at rem
  have rem32 : (Operand.reg 3#5 : Operand 32).read s = 1#32 := by
    change ((Operand.reg 3#5 : Operand 64).read s).setWidth 32 = _
    rw [rem]
    rfl
  apply hH.weaken
  · x86_norm [effect,rem,rem32,BitVec.add_zero]
  · x86_norm [effect,rem,rem32,BitVec.add_zero]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro,Or.inl,Or.inr,Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [effect,rem,rem32,BitVec.add_zero]

end P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderSetup
