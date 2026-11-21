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

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.OuterSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10aa73
  readable : ∀ offset ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([272,280,288,296,304,312,320,328] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([272,280,288,296,304,312,320,328] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x30, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x8c, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x7c, 0x24, 0x68, 0x48, 0x8d, 0xb4, 0x24, 0x10, 0x1, 0x0, 0x0, 0xba, 0xa8, 0x0, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10aaed
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 272) : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 280) : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 288) : Operand 64), (.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 296) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 304) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 312) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 320) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), (.mem (rspOf s + 64) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 104⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 272⟩,
      ⟨(.reg 2 : Operand 64), 168⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10aa73 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xaa73 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10aa73 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10aa73 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 64 (by simp)⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xaa78 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aa78 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 328 (by simp)
    · x86_norm
      exact hP.codeApart 328 (by simp) 0xaa78 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 328 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa80 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aa80 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa85 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aa85 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 320 (by simp)
    · x86_norm
      exact hP.codeApart 320 (by simp) 0xaa85 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 320 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa8d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aa8d 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa92 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aa92 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 312 (by simp)
    · x86_norm
      exact hP.codeApart 312 (by simp) 0xaa92 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 312 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa9a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aa9a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa9f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aa9f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 304 (by simp)
    · x86_norm
      exact hP.codeApart 304 (by simp) 0xaa9f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 304 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaaa7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aaa7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 52 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaaac (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aaac 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 57 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 296 (by simp)
    · x86_norm
      exact hP.codeApart 296 (by simp) 0xaaac 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 296 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaab4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aab4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 65 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaab9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aab9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 70 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 288 (by simp)
    · x86_norm
      exact hP.codeApart 288 (by simp) 0xaab9 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 288 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaac1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aac1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 78 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaac6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10aac6 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 83 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaacb (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aacb 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 88 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      exact hP.codeApart 280 (by simp) 0xaacb 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 280 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaad3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10aad3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 96 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 (by simp)
    · x86_norm
      exact hP.codeApart 272 (by simp) 0xaad3 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 (by simp) 0xaa73 122 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaadb (by decide))
  advance_then (lea_r64_effect_step 0x10aadb 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 104 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaae0 (by decide))
  advance_then (lea_r64_effect_step 0x10aae0 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 109 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaae8 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10aae8 0xba (by decide) 168)
  case sub => exact codeRange_slice_subset 0x10aa73 bytes 117 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaaed (by decide))
  advance_finish [effect]

end P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.OuterSetup
