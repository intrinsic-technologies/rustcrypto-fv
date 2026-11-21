import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d63f
  pointer : MemReadable s ((Operand.reg 13 : Operand 64).read s) 8
  length : MemReadable s ((Operand.reg 13 : Operand 64).read s + 8) 8
  position : MemReadable s (rspOf s + 535) 1

def bytes : List UInt8 :=
  [0x4d,0x8b,0x75,0x0,0x4d,0x8b,0x7d,0x8,0xf,0xb6,0x9c,0x24,0x17,0x2,0x0,0x0,0xba,0x40,0x0,0x0,0x0,0x48,0x29,0xda,0x4c,0x89,0xfd,0x48,0x29,0xd5]

def position (s : RamState) : BitVec 64 := (memLoad s.external (rspOf s + 535) 8).setWidth 64

def length (s : RamState) : BitVec 64 := memLoad s.external ((Operand.reg 13 : Operand 64).read s + 8) 64

def effect (s : RamState) : Effect :=
  { rip := 0x10d65d
    writes := [⟨(.reg 14 : Operand 64), memLoad s.external ((Operand.reg 13 : Operand 64).read s) 64⟩,
      ⟨(.reg 15 : Operand 64), length s⟩, ⟨(.reg 3 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position s⟩,
      ⟨(.reg 5 : Operand 64), length s - (64 - position s)⟩]
    flags := some (.ofStatusFlags ((subSpec (length s) (64 - position s)).2)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10d63f bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd63f bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d63f bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d63f 0x4d (by simp [RexWPrefix]) 6 (.base 13 (.d8 0)) (by decide) rfl rfl)
  case pre => intro s h; refine ⟨h.rip, ?_⟩; change MemReadable s ((Operand.reg 13 : Operand 64).read s + 0) 8; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.pointer
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd643 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d643 0x4d (by simp [RexWPrefix]) 7 (.base 13 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm
      exact hP.length
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd647 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x10d647 3 (.sib 4 none 0 (.d32 535)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm
      exact hP.position
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd64f (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10d64f 0xba (by decide) 64)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd654 (by decide))⟩
  advance_then (show StepEffect _ _ (subR64R64Effect 0x10d654 2 3) from sub_r64_r64_effect_step 0x10d654 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd657 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10d657 0x4c 0xfd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 24 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd65a (by decide))⟩
  advance_then (show StepEffect _ _ (subR64R64Effect 0x10d65a 5 2) from sub_r64_r64_effect_step 0x10d65a 0x48 0xd5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d63f bytes 27 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd65d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, position, length, BitVec.add_zero]
  · x86_norm [effect, position, length, BitVec.add_zero]
    all_goals rfl
  · intro i; cases i <;> x86_norm [effect, position, length, BitVec.add_zero]
  · x86_norm [effect, position, length, BitVec.add_zero]

end P256.Proofs.Verifying.Message.Hash.Head
