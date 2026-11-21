import P256.Proofs.Verifying.Core.Combine.Interface
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine.FirstScalar

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10dd83
  readable : ∀ i ∈ ([800,808,816,824] : List Nat), MemReadable s (rspOf s+BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([672,680,688,696] : List Nat), MemWritable s (rspOf s+BitVec.ofNat 64 i) 8
  apart : ∀ i ∈ ([672,680,688,696] : List Nat), ∀ off len : Nat,
    off+len ≤ 118431 → RangeApart (rspOf s+BitVec.ofNat 64 i) 8
      (Extracted.textAddress+BitVec.ofNat 64 off) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x8c,0x24,0x38,0x03,0x00,0x00,0x48,0x89,0x8c,0x24,0xb8,0x02,0x00,0x00,0x48,0x8b,0x8c,0x24,0x30,0x03,0x00,0x00,0x48,0x89,0x8c,0x24,0xb0,0x02,0x00,0x00,0x48,0x8b,0x8c,0x24,0x20,0x03,0x00,0x00,0x48,0x8b,0x94,0x24,0x28,0x03,0x00,0x00,0x48,0x89,0x94,0x24,0xa8,0x02,0x00,0x00,0x48,0x89,0x8c,0x24,0xa0,0x02,0x00,0x00]

def effect (s : RamState) : Effect :=
  { rip := 0x10ddc3
    writes := [⟨(.reg 1 : Operand 64),(.mem (rspOf s+800) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(.mem (rspOf s+808) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+672) : Operand 64),(.mem (rspOf s+800) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+680) : Operand 64),(.mem (rspOf s+808) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+688) : Operand 64),(.mem (rspOf s+816) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+696) : Operand 64),(.mem (rspOf s+824) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10dd83 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10dd83 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 824)) (by decide) rfl rfl)
  case pre => intro s hp; exact ⟨hp.rip,hp.readable 824 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xdd8b (by decide))
  advance_then (mov_m64_r64_effect_step 0x10dd8b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 696)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 8 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 696 (by simp)
    · x86_norm
      exact hp.apart 696 (by simp) 0xdd8b 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 696 (by simp) 0xdd83 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdd93 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10dd93 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 816)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 16 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 816 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdd9b (by decide))
  advance_then (mov_m64_r64_effect_step 0x10dd9b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 688)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 24 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 688 (by simp)
    · x86_norm
      exact hp.apart 688 (by simp) 0xdd9b 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 688 (by simp) 0xdd83 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdda3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10dda3 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 800)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 32 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 800 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddab (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ddab 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 808)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 40 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ , ?_, ?_⟩
    · x86_norm
      exact hp.readable 808 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddb3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ddb3 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 680)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 48 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 680 (by simp)
    · x86_norm
      exact hp.apart 680 (by simp) 0xddb3 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 680 (by simp) 0xdd83 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddbb (by decide))
  advance_then (mov_m64_r64_effect_step 0x10ddbb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 672)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd83 bytes 56 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 672 (by simp)
    · x86_norm
      exact hp.apart 672 (by simp) 0xddbb 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 672 (by simp) 0xdd83 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xddc3 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Core.Combine.FirstScalar
