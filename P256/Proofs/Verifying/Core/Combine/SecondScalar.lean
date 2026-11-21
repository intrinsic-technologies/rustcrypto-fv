import P256.Proofs.Verifying.Core.Combine.Interface
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine.SecondScalar

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10ddd9
  readable : ∀ i ∈ ([832,840,848,856] : List Nat), MemReadable s (rspOf s+BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([96,104,112,120] : List Nat), MemWritable s (rspOf s+BitVec.ofNat 64 i) 8
  apart : ∀ i ∈ ([96,104,112,120] : List Nat), ∀ off len : Nat,
    off+len ≤ 118431 → RangeApart (rspOf s+BitVec.ofNat 64 i) 8
      (Extracted.textAddress+BitVec.ofNat 64 off) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x8c,0x24,0x58,0x03,0x00,0x00,0x48,0x89,0x4c,0x24,0x78,0x48,0x8b,0x8c,0x24,0x50,0x03,0x00,0x00,0x48,0x89,0x4c,0x24,0x70,0x48,0x8b,0x8c,0x24,0x40,0x03,0x00,0x00,0x48,0x8b,0xb4,0x24,0x48,0x03,0x00,0x00,0x48,0x89,0x74,0x24,0x68,0x48,0x89,0x4c,0x24,0x60]

def effect (s : RamState) : Effect :=
  { rip := 0x10de0d
    writes := [⟨(.reg 1 : Operand 64),(.mem (rspOf s+832) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(.mem (rspOf s+840) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+96) : Operand 64),(.mem (rspOf s+832) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+104) : Operand 64),(.mem (rspOf s+840) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+112) : Operand 64),(.mem (rspOf s+848) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+120) : Operand 64),(.mem (rspOf s+856) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10ddd9 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10ddd9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 856)) (by decide) rfl rfl)
  case pre => intro s hp; exact ⟨hp.rip,hp.readable 856 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xdde1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10dde1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 8 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 120 (by simp)
    · x86_norm
      exact hp.apart 120 (by simp) 0xdde1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 120 (by simp) 0xddd9 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdde6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10dde6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 848)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 13 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 848 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddee (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ddee 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 21 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 112 (by simp)
    · x86_norm
      exact hp.apart 112 (by simp) 0xddee 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 112 (by simp) 0xddd9 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddf3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ddf3 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 832)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 26 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 832 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddfb (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ddfb 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 840)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 34 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 840 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xde03 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10de03 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 42 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 104 (by simp)
    · x86_norm
      exact hp.apart 104 (by simp) 0xde03 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 104 (by simp) 0xddd9 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xde08 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10de08 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ddd9 bytes 47 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 96 (by simp)
    · x86_norm
      exact hp.apart 96 (by simp) 0xde08 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 96 (by simp) 0xddd9 52 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xde0d (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Core.Combine.SecondScalar
