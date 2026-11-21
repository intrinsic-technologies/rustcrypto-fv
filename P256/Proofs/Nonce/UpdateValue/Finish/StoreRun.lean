import P256.Proofs.Nonce.UpdateValue.Finish.State
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

def valuePointer (s : RamState) : BitVec 64 := (Operand.reg 3 : Operand 64).read s

structure StorePre (s : RamState) : Prop where
  rip : s.RIP = 0x10abe2
  readable : ∀ i ∈ ([8, 16, 24, 32] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  stackWritable : ∀ i ∈ ([72, 80, 88, 96] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rspOf s + i) 8
  stackCode : ∀ i ∈ ([72, 80, 88, 96] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  valueWritable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (valuePointer s + i) 8
  valueCode : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (valuePointer s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  valueStack : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ j ∈ ([72, 80, 88, 96] : List (BitVec 64)),
    RangeApart (valuePointer s + i) 8 (rspOf s + j) 8

theorem StorePre.stack_read {s : RamState} (pre : StorePre s) (memory : Ram) (value : BitVec 64)
    {first second : BitVec 64} (hf : first ∈ ([0, 8, 16, 24] : List (BitVec 64)))
    (hs : second ∈ ([72, 80, 88, 96] : List (BitVec 64))) :
    memLoad (memStore memory (valuePointer s + first) value) (rspOf s + second) 64 =
      memLoad memory (rspOf s + second) 64 := by
  apply P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
  exact pre.valueStack first hf second hs

def storeBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x89, 0x4c, 0x24, 0x58, 0x48, 0x8b, 0x54, 0x24, 0x8, 0x48, 0x8b, 0x74, 0x24, 0x10, 0x48, 0x89, 0x74, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x48, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4b, 0x10, 0x48, 0x89, 0x73, 0x8, 0x48, 0x89, 0x13]

def storeEffect (s : RamState) : Effect :=
  { rip := 0x10ac19
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 32) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (rspOf s + 8) 64⟩,
      ⟨(.reg 6 : Operand 64), memLoad s.external (rspOf s + 16) 64⟩,
      ⟨(.mem (rspOf s + 96) : Operand 64), memLoad s.external (rspOf s + 32) 64⟩,
      ⟨(.mem (rspOf s + 88) : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
      ⟨(.mem (rspOf s + 80) : Operand 64), memLoad s.external (rspOf s + 16) 64⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), memLoad s.external (rspOf s + 8) 64⟩,
      ⟨(.mem (valuePointer s + 24) : Operand 64), memLoad s.external (rspOf s + 32) 64⟩,
      ⟨(.mem (valuePointer s + 16) : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
      ⟨(.mem (valuePointer s + 8) : Operand 64), memLoad s.external (rspOf s + 16) 64⟩,
      ⟨(.mem (valuePointer s + 0) : Operand 64), memLoad s.external (rspOf s + 8) 64⟩] }

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

set_option maxHeartbeats 2000000 in
theorem store_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StorePre (codeRange 0x10abe2 storeBytes)
      (Effect.post storeEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10abe2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 32 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0xabe7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10abe7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.stackWritable 96 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.stackCode 96 (by simp) 0xabe7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.stackCode 96 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xabec (by decide))
  advance_then (mov_r64_m64_effect_step 0x10abec 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 24 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xabf1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10abf1 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.stackWritable 88 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.stackCode 88 (by simp) 0xabf1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.stackCode 88 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xabf6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10abf6 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xabfb (by decide))
  advance_then (mov_r64_m64_effect_step 0x10abfb 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [rspOf]
      exact hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac00 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac00 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.stackWritable 80 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.stackCode 80 (by simp) 0xac00 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.stackCode 80 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac05 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac05 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.stackWritable 72 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.stackCode 72 (by simp) 0xac05 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.stackCode 72 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac0a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac0a 0x48 (by simp [RexWPrefix]) 0
    (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.valueWritable 24 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.valueCode 24 (by simp) 0xac0a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.valueCode 24 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac0e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac0e 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.valueWritable 16 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.valueCode 16 (by simp) 0xac0e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.valueCode 16 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac12 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac12 0x48 (by simp [RexWPrefix]) 6
    (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 48 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.valueWritable 8 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.valueCode 8 (by simp) 0xac12 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.valueCode 8 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac16 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ac16 0x48 (by simp [RexWPrefix]) 2
    (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10abe2 storeBytes 52 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [rspOf, valuePointer]
      exact hP.valueWritable 0 (by simp)
    · x86_norm [rspOf, valuePointer]
      exact hP.valueCode 0 (by simp) 0xac16 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [rspOf, valuePointer]
      exact hP.valueCode 0 (by simp) 0xabe2 55 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xac19 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have read := @StorePre.stack_read s hP
  simp only [valuePointer, rspOf, BitVec.ofNat_eq_ofNat] at read
  apply hH.weaken
  · x86_norm [storeEffect, valuePointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)
  · x86_norm [storeEffect, valuePointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [storeEffect, valuePointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
  · x86_norm [storeEffect, valuePointer, rspOf, read, gprNumber, rexR, modrmReg, operand_write_reg_external, operand_write_mem_external]
    all_goals (repeat constructor <;> rfl)

end P256.Proofs.Nonce.UpdateValue.Finish
