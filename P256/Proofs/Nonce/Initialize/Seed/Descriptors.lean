import P256.Proofs.Nonce.Initialize.Seed.Initialize
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure DescriptorsPre (s : RamState) : Prop where
  rip : s.RIP = 0x107bc7
  readable : ∀ i ∈ ([184, 168, 288] : List (BitVec 64)), MemReadable s (stackPtr s + i) 8
  writable : ∀ i ∈ ([104, 112, 120, 128, 136, 144] : List (BitVec 64)), MemWritable s (stackPtr s + i) 8
  codeApart : ∀ i ∈ ([104, 112, 120, 128, 136, 144] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def descriptorsBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89, 0x5c, 0x24, 0x70, 0x4c, 0x89, 0x64, 0x24, 0x78, 0x48, 0x89, 0x9c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x7c, 0x24, 0x8, 0x48, 0x8d, 0x74, 0x24, 0x68, 0xba, 0x3, 0x0, 0x0, 0x0]

def descriptorsEffect (s : RamState) : Effect :=
  let sp := (Operand.reg 4 : Operand 64).read s
  { rip := 0x107c15
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (sp + 288) 64⟩,
      ⟨(.reg 7 : Operand 64), sp + 8⟩,
      ⟨(.reg 6 : Operand 64), sp + 104⟩,
      ⟨(.reg 2 : Operand 64), 3⟩,
      ⟨(.mem (sp + 104) : Operand 64), memLoad s.external (sp + 184) 64⟩,
      ⟨(.mem (sp + 112) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem (sp + 120) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.mem (sp + 128) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem (sp + 136) : Operand 64), memLoad s.external (sp + 168) 64⟩,
      ⟨(.mem (sp + 144) : Operand 64), memLoad s.external (sp + 288) 64⟩] }

set_option maxHeartbeats 1200000 in
theorem descriptors_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DescriptorsPre (codeRange 0x107bc7 descriptorsBytes)
      (Effect.post descriptorsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107bc7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 184 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x7bcf (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bcf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 (by simp)
    · x86_norm
      exact hP.codeApart 104 (by simp) 0x7bcf 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bd4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bd4 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 (by simp)
    · x86_norm
      exact hP.codeApart 112 (by simp) 0x7bd4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bd9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bd9 0x4c (by simp [RexWPrefix]) 12
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 (by simp)
    · x86_norm
      exact hP.codeApart 120 (by simp) 0x7bd9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bde (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bde 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 23 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 0x7bde 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7be6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107be6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 168 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bee (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bee 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 0x7bee 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bf6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107bf6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 47 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 288 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bfe (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bfe 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 55 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 0x7bfe 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0x7bc7 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c06 (by decide))
  advance_then (lea_r64_effect_step 0x107c06 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 63 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c0b (by decide))
  advance_then (lea_r64_effect_step 0x107c0b 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 68 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c10 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x107c10 0xba (by decide) 3)
  case sub => exact codeRange_slice_subset 0x107bc7 descriptorsBytes 73 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c15 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have reg12 : gprNumber (0#1) (rexR (UInt8.toBitVec 76)) (12#3) = 12#5 := by decide +kernel
  apply hH.weaken
  · x86_norm [descriptorsEffect]
  · x86_norm [descriptorsEffect, reg12]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [descriptorsEffect]
  · x86_norm [descriptorsEffect]

end P256.Proofs.Nonce.Initialize.Seed
