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

structure APre (s : RamState) : Prop where
  rip : s.RIP = 0x10fe25
  writable : ∀ off ∈ ([0,8,16,24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([0,8,16,24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def aBytes : List UInt8 :=
  [72, 184, 4, 0, 0, 0, 252, 255, 255, 255, 72, 137, 68, 36, 24, 72, 184, 255, 255, 255, 255, 3, 0, 0, 0, 72, 137, 68, 36, 8, 72, 199, 68, 36, 16, 0, 0, 0, 0, 72, 199, 4, 36, 252, 255, 255, 255]

def aEffect (s : RamState) : Effect :=
  { rip := 0x10fe54
    writes := [⟨(.reg 0 : Operand 64), 0x3ffffffff⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0xfffffffc00000004⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0x3ffffffff⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), 0xfffffffffffffffc⟩] }

theorem store_a [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary APre (codeRange 0x10fe25 aBytes) (Effect.post aEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x10fe25 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xfffffffc00000004)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfe2f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fe2f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe25 aBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 24 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0xfe2f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 24 (by simp) 0xfe25 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe34 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10fe34 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x3ffffffff)
  case sub => exact codeRange_slice_subset 0x10fe25 aBytes 15 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe3e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fe3e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fe25 aBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 8 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0xfe3e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 8 (by simp) 0xfe25 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe43 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fe43 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x10fe25 aBytes 30 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 16 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0xfe43 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 16 (by simp) 0xfe25 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe4c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fe4c 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0xfffffffc)
  case sub => exact codeRange_slice_subset 0x10fe25 aBytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 0 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 0 (by simp) 0xfe4c 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 0 (by simp) 0xfe25 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfe54 (by decide))
  advance_finish [aEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Sec1.Decompress.Cubic
