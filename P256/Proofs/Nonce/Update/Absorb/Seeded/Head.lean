import P256.Proofs.Nonce.Update.Absorb.Prefix.Head
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a2c3
  pointer : MemReadable s ((Operand.reg 14 : Operand 64).read s) 8
  length : MemReadable s ((Operand.reg 14 : Operand 64).read s + 8) 8
  position : MemReadable s (rspOf s + 215) 1

def bytes : List UInt8 := [0x4d, 0x8b, 0x26, 0x4d, 0x8b, 0x7e, 0x8, 0xf, 0xb6, 0xbc, 0x24, 0xd7, 0x0, 0x0, 0x0, 0xba, 0x40, 0x0, 0x0, 0x0, 0x48, 0x29, 0xfa, 0x4c, 0x89, 0xfb, 0x48, 0x29, 0xd3]

def position (s : RamState) : BitVec 64 := (memLoad s.external (rspOf s + 215) 8).setWidth 64

def length (s : RamState) : BitVec 64 := memLoad s.external ((Operand.reg 14 : Operand 64).read s + 8) 64

def effect (s : RamState) : Effect :=
  { rip := 0x10a2e0
    writes := [⟨(.reg 12 : Operand 64), memLoad s.external ((Operand.reg 14 : Operand 64).read s) 64⟩,
      ⟨(.reg 15 : Operand 64), length s⟩, ⟨(.reg 7 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position s⟩,
      ⟨(.reg 3 : Operand 64), length s - (64 - position s)⟩]
    flags := some (.ofStatusFlags ((subSpec (length s) (64 - position s)).2)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a2c3 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa2c3 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a2c3 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10a2c3 0x4d (by simp [RexWPrefix]) 4 (.base 14 .none) (by decide) rfl rfl)
  case pre => intro s h; refine ⟨h.rip, ?_⟩; change MemReadable s ((Operand.reg 14 : Operand 64).read s + 0) 8; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.pointer
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa2c6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a2c6 0x4d (by simp [RexWPrefix]) 7 (.base 14 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm
      exact hP.length
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa2ca (by decide))
  advance_then (movzx_r32_m8_effect_step 0x10a2ca 7 (.sib 4 none 0 (.d32 215)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 7 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm
      exact hP.position
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa2d2 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a2d2 0xba (by decide) 64)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2d7 (by decide))⟩
  advance_then (show StepEffect _ _ (subR64R64Effect 0x10a2d7 2 7) from sub_r64_r64_effect_step 0x10a2d7 0x48 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2da (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10a2da 0x4c 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 23 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2dd (by decide))⟩
  advance_then (show StepEffect _ _ (subR64R64Effect 0x10a2dd 3 2) from sub_r64_r64_effect_step 0x10a2dd 0x48 0xd3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a2c3 bytes 26 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2e0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, position, length, BitVec.add_zero]
  · x86_norm [effect, position, length, BitVec.add_zero]
    all_goals rfl
  · intro i; cases i <;> x86_norm [effect, position, length, BitVec.add_zero]
  · x86_norm [effect, position, length, BitVec.add_zero]

end P256.Proofs.Nonce.Update.Absorb.Seeded.Head
