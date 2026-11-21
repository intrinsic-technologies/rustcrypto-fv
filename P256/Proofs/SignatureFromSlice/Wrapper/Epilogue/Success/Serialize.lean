import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure SerializePre (s : RamState) : Prop where
  rip : s.RIP = 0x1022b7
  readable : ∀ off ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([8,16,24,32,40,48,56,64] : List Nat), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def serializeBytes : List UInt8 :=
  [72, 139, 68, 36, 8, 72, 139, 76, 36, 16, 72, 139, 84, 36, 24, 72, 139, 116, 36, 32, 72, 139, 124, 36, 40, 76, 139, 68, 36, 48, 76, 139, 76, 36, 56, 76, 139, 84, 36, 64, 72, 15, 207, 73, 15, 200, 73, 15, 201, 73, 15, 202, 72, 15, 200, 72, 15, 201, 72, 15, 202, 72, 15, 206, 72, 137, 115, 8, 72, 137, 83, 16, 72, 137, 75, 24, 72, 137, 67, 32, 76, 137, 83, 40, 76, 137, 75, 48, 76, 137, 67, 56, 72, 137, 123, 64]

def serializeEffect (s : RamState) : Effect :=
  { rip := 0x102317
    writes := [⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 8#64) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 16#64) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 24#64) 64)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 32#64) 64)⟩,
      ⟨(.reg 7 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 40#64) 64)⟩,
      ⟨(.reg 8 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 48#64) 64)⟩,
      ⟨(.reg 9 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 56#64) 64)⟩,
      ⟨(.reg 10 : Operand 64), bswap64 (memLoad s.external (stackPtr s + 64#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 32#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 24#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 16#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 8#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 40#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 64#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 48#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 56#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 56#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 48#64) 64)⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 64#64) : Operand 64), bswap64 (memLoad s.external (stackPtr s + 40#64) 64)⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem serialize [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SerializePre (codeRange 0x1022b7 serializeBytes)
      (Effect.post serializeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1022b7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 8 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x22bc (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022bc 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22c1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022c1 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22c6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022c6 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 32 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22cb (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022cb 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 40 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22d0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022d0 0x4c (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 48 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22d5 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022d5 0x4c (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 56 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22da (by decide))
  advance_then (mov_r64_m64_effect_step 0x1022da 0x4c (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 64 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22df (by decide))
  advance_then (bswap_r64_effect_step 0x1022df 7)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 40 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22e2 (by decide))
  advance_then (bswap_r64_effect_step 0x1022e2 8)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 43 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22e5 (by decide))
  advance_then (bswap_r64_effect_step 0x1022e5 9)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 46 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22e8 (by decide))
  advance_then (bswap_r64_effect_step 0x1022e8 10)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 49 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22eb (by decide))
  advance_then (bswap_r64_effect_step 0x1022eb 0)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 52 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22ee (by decide))
  advance_then (bswap_r64_effect_step 0x1022ee 1)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 55 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22f1 (by decide))
  advance_then (bswap_r64_effect_step 0x1022f1 2)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 58 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22f4 (by decide))
  advance_then (bswap_r64_effect_step 0x1022f4 6)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 61 3
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem (by simp [bswapR64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · exact hH.rip
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22f7 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1022f7 0x48 (by simp [RexWPrefix]) 6
    (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 64 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0x22f7 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22fb (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1022fb 0x48 (by simp [RexWPrefix]) 2
    (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 68 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x22fb 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x22ff (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1022ff 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 72 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x22ff 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2303 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102303 0x48 (by simp [RexWPrefix]) 0
    (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 76 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x2303 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 32 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2307 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102307 0x4c (by simp [RexWPrefix]) 2
    (.base 3 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 80 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x2307 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x230b (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10230b 0x4c (by simp [RexWPrefix]) 1
    (.base 3 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 84 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 48 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0x230b 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x230f (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10230f 0x4c (by simp [RexWPrefix]) 0
    (.base 3 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 88 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 56 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0x230f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2313 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102313 0x48 (by simp [RexWPrefix]) 7
    (.base 3 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1022b7 serializeBytes 92 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 64 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 64 (by simp) 0x2313 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 64 (by simp) 0x22b7 96 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2317 (by decide))
  advance_finish [serializeEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success
