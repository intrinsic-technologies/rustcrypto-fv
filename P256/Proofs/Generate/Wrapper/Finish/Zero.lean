import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

structure ZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x106e7c
  writable : ∀ off ∈ ([8,16,24,32,80,88,96,104] : List Nat),
    CrossPageStore.Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([8,16,24,32,80,88,96,104] : List Nat), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def zeroBytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x8,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x10,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x18,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x20,0x0,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x8,0x48,0x89,0x44,0x24,0x50,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0x44,0x24,0x58,0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x44,0x24,0x60,0x48,0x8b,0x44,0x24,0x20,0x48,0x89,0x44,0x24,0x68]

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x106ec8
    writes := [⟨(.reg 0 : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 8#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 16#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 24#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 80#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 88#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 96#64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 104#64) : Operand 64), 0⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem zeroize [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x106e7c zeroBytes)
      (Effect.post zeroEffect) := by
  advance_begin (CrossPageStore.mov_m64_imm32_effect_step_any 0x106e7c 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 8 (by simp),h.codeApart 8 (by simp) 0x6e7c 9 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6e85 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 8 (by simp) 0x6e7c 76 (by decide)
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x106e85 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x6e85 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6e8e (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x106e8e 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x6e8e 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6e97 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x106e97 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 32 (by simp) 0x6e97 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 32 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ea0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106ea0 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using (hP.writable 8 (by simp)).toMemReadable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ea5 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106ea5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 41 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 80 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 80 (by simp) 0x6ea5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 80 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6eaa (by decide))
  advance_then (mov_r64_m64_effect_step 0x106eaa 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 46 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using (hP.writable 16 (by simp)).toMemReadable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6eaf (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106eaf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 51 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 88 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 88 (by simp) 0x6eaf 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 88 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6eb4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106eb4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 56 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using (hP.writable 24 (by simp)).toMemReadable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6eb9 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106eb9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 61 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 96 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 96 (by simp) 0x6eb9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 96 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ebe (by decide))
  advance_then (mov_r64_m64_effect_step 0x106ebe 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 66 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using (hP.writable 32 (by simp)).toMemReadable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ec3 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106ec3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106e7c zeroBytes 71 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.writable 104 (by simp)
    · x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 104 (by simp) 0x6ec3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [stackPtr, Operand.read_reg64, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hP.codeApart 104 (by simp) 0x6e7c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6ec8 (by decide))
  advance_finish [zeroEffect,stackPtr,Operand.read_reg64]

end P256.Proofs.Generate.Wrapper.Finish
