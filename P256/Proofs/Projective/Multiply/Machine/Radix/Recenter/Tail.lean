import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Half
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions

@[x86_local] theorem cmpR64Imm8Effect_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (cmpR64Imm8Effect p dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpR64Imm8Effect, h.read_reg]
  · intro s
    simp [cmpR64Imm8Effect, Write.Full, Operand.Full]

attribute [local x86_compose] cmpR64Imm8Effect

structure TailPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ba5e
  writable : MemWritable s (halfAddress s 8) 1
  apart : RangeApart (halfAddress s 8) 1 0x10ba5e 12

def tailBytes : List UInt8 := [0x88,0x44,0x0c,0x08,0x48,0x83,0xc1,2,0x48,0x83,0xf9,0x42]

def tailEffect (s : RamState) : Effect :=
  { rip := 0x10ba6a
    writes := [⟨(Operand.reg 1 : Operand 64), (Operand.reg 1 : Operand 64).read s + 2⟩,
      ⟨(Operand.mem (halfAddress s 8) : Operand 8), (Operand.reg 0 : Operand 8).read s⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 1 : Operand 64).read s + 2) 66)) }

theorem tail_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary TailPre (codeRange 0x10ba5e tailBytes) (Effect.post tailEffect) := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x10ba5e 0 (by decide)
    (.sib 4 (some 1) 0 (.d8 8)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm [BitVec.shiftLeft_zero]
      exact h.writable
    · have hh : RangeApart (halfAddress s 8) 1 0x10ba5e 4 :=
        fun i hi j hj => h.apart i hi j (by omega)
      x86_norm [BitVec.shiftLeft_zero, halfAddress] at hh ⊢
      exact hh
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [BitVec.shiftLeft_zero, halfAddress]
    exact h.apart
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xba62 (by decide))
  advance_then (add_r64_imm8_effect_step 0x10ba62 0x48 0xc1 2 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ba5e tailBytes 4 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xba66 (by decide))⟩
  advance_then (cmp_r64_imm8_effect_step 0x10ba66 0x48 0xf9 66 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ba5e tailBytes 8 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xba6a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tailEffect,halfAddress,BitVec.shiftLeft_zero]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [tailEffect,halfAddress,BitVec.shiftLeft_zero]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [tailEffect,halfAddress,BitVec.shiftLeft_zero]
    all_goals rfl
  · x86_norm [tailEffect,halfAddress,BitVec.shiftLeft_zero]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]


end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
