import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
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

namespace P256.Proofs.Nonce.Update.Prepare.Assemble.OuterSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a0a6
  readable : ∀ offset ∈ ([88,96,104,112,120,128,136,144] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([432,440,448,456,464,472,480,488] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([432,440,448,456,464,472,480,488] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xe0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x84, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x8b, 0x4c, 0x24, 0x60, 0x48, 0x89, 0x8c, 0x24, 0xb8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a117
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 432) : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 440) : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 448) : Operand 64), (.mem (rspOf s + 104) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 456) : Operand 64), (.mem (rspOf s + 112) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 464) : Operand 64), (.mem (rspOf s + 120) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 472) : Operand 64), (.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 480) : Operand 64), (.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 488) : Operand 64), (.mem (rspOf s + 144) : Operand 64).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a0a6 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa0a6 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a0a6 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10a0a6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 144 (by simp)⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa0ae (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0ae 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 488)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 488 (by simp)
    · x86_norm
      exact hP.codeApart 488 (by simp) 0xa0ae 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 488 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0b6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0b6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0be (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0be 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 480)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 480 (by simp)
    · x86_norm
      exact hP.codeApart 480 (by simp) 0xa0be 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 480 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0c6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0c6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0ce (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0ce 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 472)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 472 (by simp)
    · x86_norm
      exact hP.codeApart 472 (by simp) 0xa0ce 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 472 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0d6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0d6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 48 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0db (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0db 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 464)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 53 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 464 (by simp)
    · x86_norm
      exact hP.codeApart 464 (by simp) 0xa0db 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 464 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0e3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0e3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 61 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0e8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0e8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 456)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 66 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 456 (by simp)
    · x86_norm
      exact hP.codeApart 456 (by simp) 0xa0e8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 456 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0f0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0f0 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0f5 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a0f5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 448)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 79 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 448 (by simp)
    · x86_norm
      exact hP.codeApart 448 (by simp) 0xa0f5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 448 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa0fd (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a0fd 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 87 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa102 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a102 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 92 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 96 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa107 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a107 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 97 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 440 (by simp)
    · x86_norm
      exact hP.codeApart 440 (by simp) 0xa107 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 440 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa10f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a10f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a0a6 bytes 105 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 432 (by simp)
    · x86_norm
      exact hP.codeApart 432 (by simp) 0xa10f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 432 (by simp) 0xa0a6 113 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa117 (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Prepare.Assemble.OuterSetup
