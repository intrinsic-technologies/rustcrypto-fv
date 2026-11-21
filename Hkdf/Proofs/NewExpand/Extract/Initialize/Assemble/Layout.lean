import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import Hkdf.Proofs.Common.Instructions.RepMovsq.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.SHA256

open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

structure LayoutPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fbbf
  readable : ∀ i ∈ ([40,48,56,64,72,0,8,16,24,32] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([264,272,280,288,296,304,312,320,328,336] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  lengthWritable : MemWritable s (rspOf s + 183) 1
  codeApart : ∀ i ∈ ([264,272,280,288,296,304,312,320,328,336] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 0x10fbbf 161
  lengthCodeApart : RangeApart (rspOf s + 183) 1 0x10fbbf 161

def layoutBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x48,0x48,0x89,0x84,0x24,0x50,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x40,0x48,0x89,0x84,0x24,0x48,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x38,0x48,0x89,0x84,0x24,0x40,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x28,0x48,0x8b,0x4c,0x24,0x30,0x48,0x89,0x8c,0x24,0x38,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x30,0x1,0x0,0x0,0x48,0x8b,0x4,0x24,0x48,0x8b,0x4c,0x24,0x8,0x48,0x89,0x84,0x24,0x8,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x10,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0x84,0x24,0x18,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x84,0x24,0x20,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x20,0x48,0x89,0x84,0x24,0x28,0x1,0x0,0x0,0xc6,0x84,0x24,0xb7,0x0,0x0,0x0,0x0,0x48,0x8d,0x84,0x24,0xb8,0x0,0x0,0x0,0x48,0x8d,0xb4,0x24,0x8,0x1,0x0,0x0,0xb9,0xa,0x0,0x0,0x0,0x48,0x89,0xc7]

def layoutEffect (s : RamState) : Effect :=
  { rip := 0x10fc60
    writes := [⟨(.reg 0 : Operand 64), rspOf s + 184⟩,
      ⟨(.reg 1 : Operand 64), 10⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 184⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 264⟩,
      ⟨(.mem (rspOf s + 183) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s + 336) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), (.mem (rspOf s + 64) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 320) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 304) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 312) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 264) : Operand 64), (.mem (rspOf s) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 272) : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 280) : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 288) : Operand 64), (.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 296) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩] }

set_option maxHeartbeats 1800000 in
theorem layout_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LayoutPre (codeRange 0x10fbbf layoutBytes)
      (Effect.post layoutEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fbbf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 72 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfbc4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fbc4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 336 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 336 (by simp) a ha (5+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 336 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbcc (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fbcc 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 64 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbd1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fbd1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 18 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 328 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 328 (by simp) a ha (18+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 328 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbd9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fbd9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 26 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbde (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fbde 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 31 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 320 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 320 (by simp) a ha (31+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 320 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbe6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fbe6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 39 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbeb (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fbeb 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 44 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbf0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fbf0 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 49 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 312 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 312 (by simp) a ha (49+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 312 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfbf8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fbf8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 57 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 304 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 304 (by simp) a ha (57+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 304 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc00 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fc00 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 65 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc04 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fc04 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 69 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc09 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc09 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 74 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 264 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 264 (by simp) a ha (74+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 264 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc11 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc11 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 82 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 272 (by simp) a ha (82+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc19 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fc19 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 90 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc1e (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc1e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 95 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 280 (by simp) a ha (95+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 280 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc26 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fc26 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 103 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc2b (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc2b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 108 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 288 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 288 (by simp) a ha (108+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 288 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc33 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fc33 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 116 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc38 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fc38 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 121 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 296 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 296 (by simp) a ha (121+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 296 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc40 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10fc40 (.sib 4 none 0 (.d32 183)) (by decide) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 129 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.lengthWritable
    · x86_norm
      intro a ha b hb
      have separate := hP.lengthCodeApart a ha (129+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.lengthCodeApart
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc48 (by decide))
  advance_then (lea_r64_effect_step 0x10fc48 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 137 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc50 (by decide))
  advance_then (lea_r64_effect_step 0x10fc50 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 145 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc58 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10fc58 0xb9 (by decide) 10)
  try (case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 153 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfc5d (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fc5d 0x48 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fbbf layoutBytes 158 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xfc60 (by decide))⟩
  advance_finish [layoutEffect, BitVec.add_zero]

end Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble
