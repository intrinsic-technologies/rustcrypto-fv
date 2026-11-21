import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Program.ReadWrite.Bytes
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fd41
  readable : ∀ i ∈ ([80,88,96,104] : List (BitVec 64)), MemReadable s (stackPtr s+i) 8
  writable : ∀ i ∈ ([256,264,272,280] : List (BitVec 64)), MemWritable s (stackPtr s+i) 8
  codeApart : ∀ i ∈ ([256,264,272,280] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+i) 8 (Extracted.textAddress+BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x8b, 0x4c, 0x24, 0x58, 0x48, 0x89, 0x8c, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x0, 0x1, 0x0, 0x0]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x10fd75
    writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (stackPtr s+80) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem (stackPtr s+88) : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+256) : Operand 64), (Operand.mem (stackPtr s+80) : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+264) : Operand 64), (Operand.mem (stackPtr s+88) : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+272) : Operand 64), (Operand.mem (stackPtr s+96) : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+280) : Operand 64), (Operand.mem (stackPtr s+104) : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem copy_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x10fd41 copyBytes) (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fd41 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable 104 (by simp)⟩
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xfd46 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fd46 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      exact hP.codeApart 280 (by simp) 0xfd46 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 280 (by simp) 0xfd41 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd4e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fd4e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd53 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fd53 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 (by simp)
    · x86_norm
      exact hP.codeApart 272 (by simp) 0xfd53 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 (by simp) 0xfd41 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd5b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fd5b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 80 (by simp)
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd60 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fd60 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 31 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by simp)
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd65 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fd65 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 264 (by simp)
    · x86_norm
      exact hP.codeApart 264 (by simp) 0xfd65 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 264 (by simp) 0xfd41 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd6d (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fd6d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fd41 copyBytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 256 (by simp)
    · x86_norm
      exact hP.codeApart 256 (by simp) 0xfd6d 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 256 (by simp) 0xfd41 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd75 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  have h280_96 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (stackPtr s+280) v) (stackPtr s+96) 64 = memLoad m (stackPtr s+96) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (RangeApart.offsets (stackPtr s)
      (a := 280) (b := 96) (by decide) (by decide) (.inr (by decide)))
  have h280_80 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (stackPtr s+280) v) (stackPtr s+80) 64 = memLoad m (stackPtr s+80) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (RangeApart.offsets (stackPtr s)
      (a := 280) (b := 80) (by decide) (by decide) (.inr (by decide)))
  have h280_88 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (stackPtr s+280) v) (stackPtr s+88) 64 = memLoad m (stackPtr s+88) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (RangeApart.offsets (stackPtr s)
      (a := 280) (b := 88) (by decide) (by decide) (.inr (by decide)))
  have h272_80 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (stackPtr s+272) v) (stackPtr s+80) 64 = memLoad m (stackPtr s+80) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (RangeApart.offsets (stackPtr s)
      (a := 272) (b := 80) (by decide) (by decide) (.inr (by decide)))
  have h272_88 (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (stackPtr s+272) v) (stackPtr s+88) 64 = memLoad m (stackPtr s+88) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (RangeApart.offsets (stackPtr s)
      (a := 272) (b := 88) (by decide) (by decide) (.inr (by decide)))
  simp only [BitVec.ofNat_eq_ofNat] at h280_96 h280_80 h280_88 h272_80 h272_88
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, stackPtr, operand_write_reg_external, operand_write_mem_external, h280_96, h280_80, h280_88, h272_80, h272_88]
    simp [Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect, stackPtr]
    simp [Operand.read_reg64]

end P256.Proofs.Sec1.Decompress.Input
