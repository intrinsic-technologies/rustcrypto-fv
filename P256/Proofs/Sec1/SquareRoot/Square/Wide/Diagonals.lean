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

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult shldR64R64OneEffect_components shld_r64_r64_one_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure DiagonalsPre (s : RamState) : Prop where
  rip : s.RIP = 0x11cc33
  readable : ∀ i ∈ ([32] : List (BitVec 64)), MemReadable s (((Operand.reg 4 : Operand 64).read s) + i) 8
  writable : ∀ i ∈ ([8, 16, 24] : List (BitVec 64)), MemWritable s (((Operand.reg 4 : Operand 64).read s) + i) 8
  codeApart : ∀ i ∈ ([8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (((Operand.reg 4 : Operand 64).read s) + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def diagonalsBytes : List UInt8 :=
  [0x4c, 0x89, 0xf8, 0x49, 0xf7, 0xe7, 0x48, 0x89, 0x44, 0x24, 0x8, 0x49, 0x89, 0xd7, 0x4c, 0x89, 0xe6, 0x4c, 0xf, 0xa4, 0xc6, 0x1, 0x4c, 0x89, 0xf0, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x89, 0xd6, 0x49, 0x89, 0xca, 0x4d, 0xf, 0xa4, 0xea, 0x1, 0x4c, 0x89, 0xd8, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xd3, 0x48, 0x89, 0xc5, 0x4c, 0x89, 0xc8, 0x49, 0xf7, 0xe1, 0x48, 0x89, 0x44, 0x24, 0x10, 0x49, 0x89, 0xd9, 0x49, 0xc1, 0xe9, 0x3f, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x49, 0xf, 0xa4, 0xc5, 0x1]

def diagonalsEffect (s : RamState) : Effect :=
  let v111bd6 := ((Operand.reg 15 : Operand 64).read s) * ((Operand.reg 15 : Operand 64).read s)
  let hv111bd6 := mulHigh64 ((Operand.reg 15 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)
  let v111be4 := shldOneResult ((Operand.reg 12 : Operand 64).read s) ((Operand.reg 8 : Operand 64).read s)
  let v111bec := ((Operand.reg 14 : Operand 64).read s) * ((Operand.reg 14 : Operand 64).read s)
  let hv111bec := mulHigh64 ((Operand.reg 14 : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s)
  let v111bfa := shldOneResult ((Operand.reg 1 : Operand 64).read s) ((Operand.reg 13 : Operand 64).read s)
  let v111c02 := ((Operand.reg 11 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let hv111c02 := mulHigh64 ((Operand.reg 11 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let v111c0e := ((Operand.reg 9 : Operand 64).read s) * ((Operand.reg 9 : Operand 64).read s)
  let hv111c0e := mulHigh64 ((Operand.reg 9 : Operand 64).read s) ((Operand.reg 9 : Operand 64).read s)
  let v111c19 := ((Operand.reg 3 : Operand 64).read s) >>> 63
  let v111c22 := shldOneResult ((Operand.reg 13 : Operand 64).read s) ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64).read s)
  { rip := 0x11cc87
    writes := [
      ⟨(.reg 0 : Operand 64), ((Operand.mem (((Operand.reg 4 : Operand 64).read s) + 32) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), hv111c0e⟩,
      ⟨(.reg 5 : Operand 64), v111c02⟩,
      ⟨(.reg 6 : Operand 64), v111be4⟩,
      ⟨(.reg 9 : Operand 64), v111c19⟩,
      ⟨(.reg 10 : Operand 64), v111bfa⟩,
      ⟨(.reg 11 : Operand 64), hv111c02⟩,
      ⟨(.reg 13 : Operand 64), v111c22⟩,
      ⟨(.reg 14 : Operand 64), hv111bec⟩,
      ⟨(.reg 15 : Operand 64), hv111bd6⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 8) : Operand 64), v111bd6⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 16) : Operand 64), v111c0e⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s) + 24) : Operand 64), v111bec⟩]
    flags := some (⟨none, none, none, none, none, none⟩) }

set_option maxHeartbeats 1200000 in
theorem diagonals_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DiagonalsPre (codeRange 0x11cc33 diagonalsBytes)
      (Effect.post diagonalsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x11cc33 0x4c 0xf8 (by simp [RexWPrefix]) (by decide))
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc36 (by decide))
  advance_then (mul_r64_effect_step 0x11cc36 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc39 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11cc39 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 6 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x1cc39 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1cc33 84 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc3e (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc3e 0x49 0xd7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc41 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc41 0x4c 0xe6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc44 (by decide))
  advance_then (shld_r64_r64_one_effect_step 0x11cc44 0x4c 0xc6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 17 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [shldR64R64OneEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc49 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc49 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc4c (by decide))
  advance_then (mul_r64_effect_step 0x11cc4c 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc4f (by decide))
  advance_then (mov_m64_r64_effect_step 0x11cc4f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x1cc4f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x1cc33 84 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc54 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc54 0x49 0xd6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 33 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc57 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc57 0x49 0xca (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 36 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc5a (by decide))
  advance_then (shld_r64_r64_one_effect_step 0x11cc5a 0x4d 0xea (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [shldR64R64OneEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc5f (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc5f 0x4c 0xd8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 44 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc62 (by decide))
  advance_then (mul_r64_effect_step 0x11cc62 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 47 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc65 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc65 0x49 0xd3 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 50 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc68 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc68 0x48 0xc5 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 53 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc6b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc6b 0x4c 0xc8 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 56 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc6e (by decide))
  advance_then (mul_r64_effect_step 0x11cc6e 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 59 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [mulR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc71 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11cc71 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 62 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x1cc71 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x1cc33 84 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc76 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11cc76 0x49 0xd9 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 67 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc79 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x11cc79 0x49 0xe9 0x3f (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 70 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc7d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11cc7d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 74 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc82 (by decide))
  advance_then (shld_r64_r64_one_effect_step 0x11cc82 0x49 0xc5 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11cc33 diagonalsBytes 79 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [shldR64R64OneEffect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cc87 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [diagonalsEffect]
  · x86_norm [diagonalsEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [diagonalsEffect] <;> rfl
  · x86_norm [diagonalsEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
