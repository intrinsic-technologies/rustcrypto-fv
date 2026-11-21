import P256.Proofs.Sec1.SquareRoot.Square.Wide.Common
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulFlags64 mulHigh64 mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LowerProductsPre (s : RamState) : Prop where
  rip : s.RIP = 0x11cbb8
  readable : ∀ i ∈ ([0, 8, 16] : List (BitVec 64)), MemReadable s (((Operand.reg 6 : Operand 64).read s) + i) 8
  writable : ∀ i ∈ ([8, 32] : List (BitVec 64)), MemWritable s (((Operand.reg 4 : Operand 64).read s) + i) 8
  codeApart : ∀ i ∈ ([8, 32] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (((Operand.reg 4 : Operand 64).read s) + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def lowerProductsBytes : List UInt8 :=
  [0x4c, 0x8b, 0xe, 0x4c, 0x8b, 0x5e, 0x8, 0x4c, 0x8b, 0x76, 0x10, 0x4c, 0x89, 0xc8, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xd2, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe1, 0x49, 0x89, 0xc5, 0x48, 0x89, 0x54, 0x24, 0x8]

def lowerProductsEffect (s : RamState) : Effect :=
  let a0 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 0) : Operand 64).read s)
  let a1 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s)
  let a2 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  { rip := 0x11cbdf
    writes := [
      ⟨(.reg 9 : Operand 64), a0⟩,
      ⟨(.reg 11 : Operand 64), a1⟩,
      ⟨(.reg 14 : Operand 64), a2⟩,
      ⟨(.reg 10 : Operand 64), mulHigh64 a0 a1⟩,
      ⟨(.reg 0 : Operand 64), a2*a0⟩,
      ⟨(.reg 2 : Operand 64), mulHigh64 a2 a0⟩,
      ⟨(.reg 13 : Operand 64), a2*a0⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64), a0*a1⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), mulHigh64 a2 a0⟩]
    flags := some (mulFlags64 a2 a0) }

set_option maxHeartbeats 1200000 in
theorem lowerProducts_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LowerProductsPre (codeRange 0x11cbb8 lowerProductsBytes)
      (Effect.post lowerProductsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11cbb8 0x4c (by simp [RexWPrefix]) 1 (.base 6 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 0 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbbb (by decide))
  advance_then (mov_r64_m64_effect_step 0x11cbbb 0x4c (by simp [RexWPrefix]) 3 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbbf (by decide))
  advance_then (mov_r64_m64_effect_step 0x11cbbf 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbc3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbc3 0x4c 0xc8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbc6 (by decide))
  advance_then (mul_r64_effect_step 0x11cbc6 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbc9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbc9 0x49 0xd2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbcc (by decide))
  advance_then (mov_m64_r64_effect_step 0x11cbcc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x1cbcc 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x1cbb8 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbd1 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbd1 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbd4 (by decide))
  advance_then (mul_r64_effect_step 0x11cbd4 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbd7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbd7 0x49 0xc5 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 31 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbda (by decide))
  advance_then (mov_m64_r64_effect_step 0x11cbda 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cbb8 lowerProductsBytes 34 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x1cbda 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1cbb8 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbdf (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowerProductsEffect]
  · x86_norm [lowerProductsEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [lowerProductsEffect] <;> rfl
  · x86_norm [lowerProductsEffect]

structure UpperProductsPre (s : RamState) : Prop where
  rip : s.RIP = 0x11cbdf
  readable : ∀ i ∈ ([24] : List (BitVec 64)), MemReadable s (((Operand.reg 6 : Operand 64).read s) + i) 8

def upperProductsBytes : List UInt8 :=
  [0x4c, 0x8b, 0x7e, 0x18, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe3, 0x48, 0x89, 0xd6, 0x48, 0x89, 0xc1, 0x4c, 0x89, 0xf8, 0x49, 0xf7, 0xe1, 0x49, 0x89, 0xd4, 0x48, 0x89, 0xc3, 0x4c, 0x89, 0xf8, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xc0, 0x48, 0x89, 0xd5]

def upperProductsEffect (s : RamState) : Effect :=
  let a0 := ((Operand.reg 9 : Operand 64).read s)
  let a1 := ((Operand.reg 11 : Operand 64).read s)
  let a2 := ((Operand.reg 14 : Operand 64).read s)
  let a3 := ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)
  { rip := 0x11cc07
    writes := [
      ⟨(.reg 15 : Operand 64), a3⟩,
      ⟨(.reg 6 : Operand 64), mulHigh64 a2 a1⟩,
      ⟨(.reg 1 : Operand 64), a2*a1⟩,
      ⟨(.reg 12 : Operand 64), mulHigh64 a3 a0⟩,
      ⟨(.reg 3 : Operand 64), a3*a0⟩,
      ⟨(.reg 8 : Operand 64), a3*a1⟩,
      ⟨(.reg 5 : Operand 64), mulHigh64 a3 a1⟩,
      ⟨(.reg 0 : Operand 64), a3*a1⟩,
      ⟨(.reg 2 : Operand 64), mulHigh64 a3 a1⟩]
    flags := some (mulFlags64 a3 a1) }

set_option maxHeartbeats 1200000 in
theorem upperProducts_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary UpperProductsPre (codeRange 0x11cbdf upperProductsBytes)
      (Effect.post upperProductsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11cbdf 0x4c (by simp [RexWPrefix]) 7 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 24 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbe3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbe3 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbe6 (by decide))
  advance_then (mul_r64_effect_step 0x11cbe6 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbe9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbe9 0x48 0xd6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbec (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbec 0x48 0xc1 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbef (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbef 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbf2 (by decide))
  advance_then (mul_r64_effect_step 0x11cbf2 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbf5 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbf5 0x49 0xd4 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbf8 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbf8 0x48 0xc3 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbfb (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cbfb 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cbfe (by decide))
  advance_then (mul_r64_effect_step 0x11cbfe 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 31 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc01 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc01 0x49 0xc0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 34 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc04 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc04 0x48 0xd5 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cbdf upperProductsBytes 37 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc07 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [upperProductsEffect]
  · x86_norm [upperProductsEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [upperProductsEffect] <;> rfl
  · x86_norm [upperProductsEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
