import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
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

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fe7d
  writable : ∀ off ∈ ([0,8,16,24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([0,8,16,24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bBytes : List UInt8 :=
  [72, 184, 52, 72, 135, 4, 29, 6, 48, 220, 72, 137, 68, 36, 24, 72, 184, 214, 46, 33, 247, 171, 32, 162, 229, 72, 137, 68, 36, 16, 72, 184, 144, 48, 132, 120, 205, 5, 240, 172, 72, 137, 68, 36, 8, 72, 184, 223, 189, 196, 41, 98, 223, 156, 216, 72, 137, 4, 36]

def bEffect (s : RamState) : Effect :=
  { rip := 0x10feb8
    writes := [⟨(.reg 0 : Operand 64), 0xd89cdf6229c4bddf⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0xdc30061d04874834⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0xe5a220abf7212ed6⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0xacf005cd78843090⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), 0xd89cdf6229c4bddf⟩] }

theorem store_b [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BPre (codeRange 0x10fe7d bBytes) (Effect.post bEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x10fe7d 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xdc30061d04874834)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfe87 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fe87 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0xfe87 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0xfe7d 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe8c (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10fe8c 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xe5a220abf7212ed6)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 15 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe96 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fe96 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0xfe96 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0xfe7d 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe9b (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10fe9b 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xacf005cd78843090)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 30 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfea5 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fea5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0xfea5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0xfe7d 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfeaa (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10feaa 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xd89cdf6229c4bddf)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 45 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfeb4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10feb4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe7d bBytes 55 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 0 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 0 (by simp) 0xfeb4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 0 (by simp) 0xfe7d 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfeb8 (by decide))
  advance_finish [bEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Decompress.Cubic
