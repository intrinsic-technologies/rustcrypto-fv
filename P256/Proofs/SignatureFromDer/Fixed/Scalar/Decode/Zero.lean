import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fa6c
  writable : ∀ off ∈ ([64,56,48,40] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([64,56,48,40] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def zeroBytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x40,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x38,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x30,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x28,0x0,0x0,0x0,0x0]

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x10fa90
    writes := [⟨(.mem (stackPtr s + 64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩] }

theorem zero_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x10fa6c zeroBytes)
      (Effect.post zeroEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fa6c 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 64 (by simp), h.codeApart 64 (by simp) 0xfa6c 9 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfa75 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 64 (by simp) 0xfa6c 36 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fa75 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fa6c zeroBytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 56 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0xfa75 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 56 (by simp) 0xfa6c 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfa7e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fa7e 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fa6c zeroBytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 48 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0xfa7e 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 48 (by simp) 0xfa6c 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfa87 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fa87 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fa6c zeroBytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0xfa87 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 40 (by simp) 0xfa6c 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfa90 (by decide))
  advance_finish [zeroEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
