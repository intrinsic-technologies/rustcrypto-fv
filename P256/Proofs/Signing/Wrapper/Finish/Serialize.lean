import P256.Proofs.Signing.Wrapper.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure SerializePre (s : RamState) : Prop where
  rip : s.RIP = 0x102a50
  readable : ∀ off ∈ ([64,72,80,88,96,104,112,120,312] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    CrossPageStore.Writable s (memLoad s.external (stackPtr s + 312#64) 64 + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([8,16,24,32,40,48,56,64] : List Nat), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (memLoad s.external (stackPtr s + 312#64) 64 + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def serializeBytes : List UInt8 :=
  [72,139,68,36,64,72,139,76,36,72,72,139,84,36,80,72,139,116,36,96,72,139,124,36,104,76,139,68,36,112,76,139,76,36,120,72,15,206,72,15,207,73,15,200,73,15,201,72,15,200,72,15,201,72,15,202,76,139,84,36,88,73,15,202,76,139,156,36,56,1,0,0,77,137,83,8,73,137,83,16,73,137,75,24,73,137,67,32,77,137,75,40,77,137,67,48,73,137,123,56,73,137,115,64]

def serializeEffect (s : RamState) : Effect :=
  { rip := 0x102ab8
    writes := [⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 64#64) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 72#64) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 80#64) 64)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 96#64) 64)⟩,
      ⟨(.reg 7 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 104#64) 64)⟩,
      ⟨(.reg 8 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 112#64) 64)⟩,
      ⟨(.reg 9 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 120#64) 64)⟩,
      ⟨(.reg 10 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 88#64) 64)⟩,
      ⟨(.reg 11 : Operand 64), memLoad s.external (stackPtr s + 312#64) 64⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 8#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 88#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 16#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 80#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 24#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 72#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 32#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 64#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 40#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 120#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 48#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 112#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 56#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 104#64) 64)⟩,
      ⟨(.mem (memLoad s.external (stackPtr s + 312#64) 64 + 64#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 96#64) 64)⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem serialize [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SerializePre (codeRange 0x102a50 serializeBytes)
      (Effect.post serializeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x102a50 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 64 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x2a55 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a55 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 72 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a5a (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a5a 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 80 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a5f (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a5f 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 96 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a64 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a64 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 104 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a69 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a69 0x4c (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 112 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a6e (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a6e 0x4c (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 120 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a73 (by decide))
  advance_then (bswap_r64_effect_step 0x102a73 6)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 35 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a76 (by decide))
  advance_then (bswap_r64_effect_step 0x102a76 7)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 38 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a79 (by decide))
  advance_then (bswap_r64_effect_step 0x102a79 8)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 41 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a7c (by decide))
  advance_then (bswap_r64_effect_step 0x102a7c 9)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 44 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a7f (by decide))
  advance_then (bswap_r64_effect_step 0x102a7f 0)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 47 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a82 (by decide))
  advance_then (bswap_r64_effect_step 0x102a82 1)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 50 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a85 (by decide))
  advance_then (bswap_r64_effect_step 0x102a85 2)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a88 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a88 0x4c (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 56 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 88 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a8d (by decide))
  advance_then (bswap_r64_effect_step 0x102a8d 10)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 61 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a90 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102a90 0x4c (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 312 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a98 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102a98 0x4d (by simp [RexWPrefix]) 2
    (.base 11 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 72 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0x2a98 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2a9c (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102a9c 0x49 (by simp [RexWPrefix]) 2
    (.base 11 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 76 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x2a9c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2aa0 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102aa0 0x49 (by simp [RexWPrefix]) 1
    (.base 11 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 80 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x2aa0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2aa4 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102aa4 0x49 (by simp [RexWPrefix]) 0
    (.base 11 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 84 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x2aa4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2aa8 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102aa8 0x4d (by simp [RexWPrefix]) 1
    (.base 11 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 88 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x2aa8 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2aac (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102aac 0x4d (by simp [RexWPrefix]) 0
    (.base 11 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 92 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 48 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0x2aac 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2ab0 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102ab0 0x49 (by simp [RexWPrefix]) 7
    (.base 11 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 96 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 56 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0x2ab0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2ab4 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102ab4 0x49 (by simp [RexWPrefix]) 6
    (.base 11 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102a50 serializeBytes 100 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 64 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 64 (by simp) 0x2ab4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 64 (by simp) 0x2a50 104 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2ab8 (by decide))
  advance_finish [serializeEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.Signing.Wrapper.Finish
