import P256.Proofs.Nonce.Update.Phases
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero.Save

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def keyPointer (s : RamState) : BitVec 64 := (Operand.mem (rspOf s + 72) : Operand 64).read s

structure StorePre (s : RamState) : Prop where
  rip : s.RIP = 0x10a3f7
  readable : ∀ i ∈ ([72, 256, 264, 272, 280] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  stackWritable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s + i) 8
  stackCode : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  keyWritable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (keyPointer s + i) 8
  keyCode : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (keyPointer s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  keyStack : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ j ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    RangeApart (keyPointer s + i) 8 (rspOf s + j) 8

theorem StorePre.stack_read {s : RamState} (pre : StorePre s) (memory : Ram) (value : BitVec 64)
    {first second : BitVec 64} (hf : first ∈ ([0, 8, 16, 24] : List (BitVec 64)))
    (hs : second ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
    memLoad (memStore memory (keyPointer s + first) value) (rspOf s + second) 64 =
      memLoad memory (rspOf s + second) 64 := by
  apply P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
  exact pre.keyStack first hf second hs

def storeBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x8c, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x8b, 0x94, 0x24, 0x0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0xb4, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x74, 0x24, 0x8, 0x48, 0x89, 0x14, 0x24, 0x48, 0x8b, 0x5c, 0x24, 0x48, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4b, 0x10, 0x48, 0x89, 0x73, 0x8, 0x48, 0x89, 0x13, 0x48, 0x89, 0xdf]

def storeEffect (s : RamState) : Effect :=
  { rip := 0x10a441
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 280) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 272) 64⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (rspOf s + 256) 64⟩,
      ⟨(.reg 7 : Operand 64), keyPointer s⟩,
      ⟨(.reg 3 : Operand 64), keyPointer s⟩,
      ⟨(.reg 6 : Operand 64), memLoad s.external (rspOf s + 264) 64⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), memLoad s.external (rspOf s + 280) 64⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), memLoad s.external (rspOf s + 272) 64⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), memLoad s.external (rspOf s + 264) 64⟩,
      ⟨(.mem (rspOf s + 0) : Operand 64), memLoad s.external (rspOf s + 256) 64⟩,
      ⟨(.mem (keyPointer s + 24) : Operand 64), memLoad s.external (rspOf s + 280) 64⟩,
      ⟨(.mem (keyPointer s + 16) : Operand 64), memLoad s.external (rspOf s + 272) 64⟩,
      ⟨(.mem (keyPointer s + 8) : Operand 64), memLoad s.external (rspOf s + 264) 64⟩,
      ⟨(.mem (keyPointer s + 0) : Operand 64), memLoad s.external (rspOf s + 256) 64⟩] }

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem store_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StorePre (codeRange 0x10a3f7 storeBytes)
      (Effect.post storeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10a3f7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 280 (by simp)⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xa3ff (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a3ff 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.stackWritable 24 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.stackCode 24 (by simp) 0xa3ff 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.stackCode 24 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa404 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a404 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 272 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa40c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a40c 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.stackWritable 16 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.stackCode 16 (by simp) 0xa40c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.stackCode 16 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa411 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a411 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 256 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa419 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a419 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 264 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa421 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a421 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.stackWritable 8 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.stackCode 8 (by simp) 0xa421 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.stackCode 8 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa426 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a426 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 47 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.stackWritable 0 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.stackCode 0 (by simp) 0xa426 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.stackCode 0 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa42a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a42a 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 51 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 72 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa42f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a42f 0x48 (by simp [RexWPrefix]) 0
    (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 56 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.keyWritable 24 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.keyCode 24 (by simp) 0xa42f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.keyCode 24 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa433 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a433 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 60 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.keyWritable 16 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.keyCode 16 (by simp) 0xa433 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.keyCode 16 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa437 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a437 0x48 (by simp [RexWPrefix]) 6
    (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 64 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.keyWritable 8 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.keyCode 8 (by simp) 0xa437 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.keyCode 8 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa43b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10a43b 0x48 (by simp [RexWPrefix]) 2
    (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 68 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, keyPointer]
      exact hP.keyWritable 0 (by simp)
    · x86_norm [rspOf, keyPointer]
      exact hP.keyCode 0 (by simp) 0xa43b 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, keyPointer]
      exact hP.keyCode 0 (by simp) 0xa3f7 74 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa43e (by decide))
  advance_then (mov_r64_r64_effect_step 0x10a43e 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a3f7 storeBytes 71 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa441 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have read := @StorePre.stack_read s hP
  simp only [keyPointer, rspOf, BitVec.ofNat_eq_ofNat] at read
  apply hH.weaken
  · x86_norm [storeEffect, keyPointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)
  · x86_norm [storeEffect, keyPointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [storeEffect, keyPointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
  · x86_norm [storeEffect, keyPointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)

end P256.Proofs.Nonce.Update.Zero.Save
