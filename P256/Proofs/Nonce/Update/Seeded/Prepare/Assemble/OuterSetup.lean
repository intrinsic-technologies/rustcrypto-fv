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

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.OuterSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a5a5
  readable : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([432,440,448,456,464,472,480,488] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([432,440,448,456,464,472,480,488] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0xe0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x4, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x8c, 0x24, 0xb8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a60c
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 0) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 432) : Operand 64), (.mem (rspOf s + 0) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 440) : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 448) : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 456) : Operand 64), (.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 464) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 472) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 480) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 488) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a5a5 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa5a5 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a5a5 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10a5a5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 56 (by simp)⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa5aa (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5aa 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 488)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 488 (by simp)
    · x86_norm
      exact hP.codeApart 488 (by simp) 0xa5aa 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 488 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5b2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5b2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5b7 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5b7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 480)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 480 (by simp)
    · x86_norm
      exact hP.codeApart 480 (by simp) 0xa5b7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 480 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5bf (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5bf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5c4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5c4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 472)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 472 (by simp)
    · x86_norm
      exact hP.codeApart 472 (by simp) 0xa5c4 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 472 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5cc (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5cc 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5d1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5d1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 464)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 464 (by simp)
    · x86_norm
      exact hP.codeApart 464 (by simp) 0xa5d1 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 464 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5d9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5d9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 52 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5de (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5de 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 456)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 57 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 456 (by simp)
    · x86_norm
      exact hP.codeApart 456 (by simp) 0xa5de 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 456 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5e6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5e6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 65 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5eb (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5eb 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 448)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 70 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 448 (by simp)
    · x86_norm
      exact hP.codeApart 448 (by simp) 0xa5eb 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 448 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5f3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5f3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 78 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5f7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a5f7 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 82 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa5fc (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a5fc 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 87 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 440 (by simp)
    · x86_norm
      exact hP.codeApart 440 (by simp) 0xa5fc 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 440 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa604 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a604 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a5a5 bytes 95 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 432 (by simp)
    · x86_norm
      exact hP.codeApart 432 (by simp) 0xa604 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 432 (by simp) 0xa5a5 103 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa60c (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.OuterSetup
