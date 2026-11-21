import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Memory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure OutputPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ off ∈ ([0,8,16,24,32] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + off) 8
  codeApart : ∀ off ∈ ([0,8,16,24,32] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def acceptBytes : List UInt8 :=
  [0x4c,0x89,0x7b,0x8,0x4c,0x89,0x63,0x10,0x4c,0x89,0x6b,0x18,0x48,0x89,0x6b,0x20,0x45,0x31,0xf6,0x4c,0x89,0x33,0x48,0x89,0xd8]

def acceptEffect (s : RamState) : Effect :=
  { rip := 0x10fb96
    writes := [⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8#64) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16#64) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24#64) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32#64) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s) : Operand 64), 0⟩,
      ⟨(.reg 0 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem accept_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (OutputPre 0x10fb7d) (codeRange 0x10fb7d acceptBytes)
      (Effect.post acceptEffect) := by
  refine AdvanceTriple.block_first ?k (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb7d 0x4c (by simp [RexWPrefix]) 7 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl) ?sub ?pre ?av ?next
  case sub => x86_sub
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · exact h.writable 8 (by simp)
    · exact h.codeApart 8 (by simp) 0xfb7d 4 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [State.regValue, BitVec.add_zero]
    exact h.codeApart 8 (by simp) 0xfb7d 25 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfb81 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb81 0x4c (by simp [RexWPrefix]) 4 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [State.regValue]
      exact hP.writable 16 (by simp)
    · x86_norm [State.regValue]
      exact hP.codeApart 16 (by simp) 0xfb81 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [State.regValue]
      exact hP.codeApart 16 (by simp) 0xfb7d 25 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb85 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb85 0x4c (by simp [RexWPrefix]) 5 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [State.regValue]
      exact hP.writable 24 (by simp)
    · x86_norm [State.regValue]
      exact hP.codeApart 24 (by simp) 0xfb85 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [State.regValue]
      exact hP.codeApart 24 (by simp) 0xfb7d 25 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb89 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb89 0x48 (by simp [RexWPrefix]) 5 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [State.regValue]
      exact hP.writable 32 (by simp)
    · x86_norm [State.regValue]
      exact hP.codeApart 32 (by simp) 0xfb89 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [State.regValue]
      exact hP.codeApart 32 (by simp) 0xfb7d 25 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb8d (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x10fb8d 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb90 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb90 0x4c (by simp [RexWPrefix]) 6 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [State.regValue]
      exact (BitVec.add_zero ((Operand.reg 3 : Operand 64).read s)) ▸ (hP.writable 0#64 (by simp))
    · x86_norm [State.regValue]
      exact (BitVec.add_zero ((Operand.reg 3 : Operand 64).read s)) ▸ (hP.codeApart 0#64 (by simp) 0xfb90 3 (by decide))
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [State.regValue]
      exact (BitVec.add_zero ((Operand.reg 3 : Operand 64).read s)) ▸ (hP.codeApart 0#64 (by simp) 0xfb7d 25 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb93 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fb93 0x48 0xd8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fb7d acceptBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb96 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [acceptEffect, State.regValue, Operand.read_reg64]
  · x86_norm [acceptEffect, State.regValue, Operand.read_reg64]
    simp [gprIndex, gprNumber, rexR, rexB, modrmRm, modrmReg,
      BitVec.xor_self]
  · intro i
    cases i <;> x86_norm [acceptEffect]
  · x86_norm [acceptEffect, State.regValue, Operand.read_reg64]
    exact BitVec.add_zero _

def rejectBytes : List UInt8 :=
  [0x4c,0x89,0x33,0x48,0x89,0xd8]

def rejectEffect (s : RamState) : Effect :=
  { rip := 0x10fb96
    writes := [⟨(.mem ((Operand.reg 3 : Operand 64).read s) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem reject_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (OutputPre 0x10fb90) (codeRange 0x10fb90 rejectBytes)
      (Effect.post rejectEffect) := by
  refine AdvanceTriple.block_first ?k (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fb90 0x4c (by simp [RexWPrefix]) 6 (.base 3 .none) (by decide +kernel) rfl rfl) ?sub ?pre ?av ?next
  case sub => x86_sub
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · exact h.writable 0#64 (by simp)
    · exact h.codeApart 0#64 (by simp) 0xfb90 3 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [State.regValue, BitVec.add_zero]
    exact (BitVec.add_zero ((Operand.reg 3 : Operand 64).read s)) ▸ (h.codeApart 0#64 (by simp) 0xfb90 6 (by decide))
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xfb93 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10fb93 0x48 0xd8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10fb90 rejectBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xfb96 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [rejectEffect, State.regValue, Operand.read_reg64]
  · x86_norm [rejectEffect, State.regValue, Operand.read_reg64]
    simp [gprIndex, gprNumber, rexR, modrmReg]
  · intro i
    cases i <;> x86_norm [rejectEffect]
  · x86_norm [rejectEffect, State.regValue, Operand.read_reg64]
    exact BitVec.add_zero _

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
