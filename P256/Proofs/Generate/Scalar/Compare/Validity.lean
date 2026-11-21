import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Generate.Scalar.Compare.Common
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Encoding.Parser.CompressedRoute (movzxAlEffect)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (andAlImm8Effect)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

attribute [local x86_compose] andAlImm8Effect movzxAlEffect

private theorem compareAndAlLocal (p : BitVec 64) (imm : BitVec 8) :
    Effect.Local (andAlImm8Effect p imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andAlImm8Effect, h.read_reg]
  · intro s
    simp [andAlImm8Effect, Write.Full, Operand.Full]

private theorem compareMovzxAlLocal (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (movzxAlEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movzxAlEffect, h.read_reg]
  · intro s
    simp [movzxAlEffect, Write.Full, Operand.Full]

attribute [local x86_local] compareAndAlLocal compareMovzxAlLocal

private theorem mergeGPR_byte_zeroExtend (x y : BitVec 8) :
    mergeGPR 8 x (y.setWidth 64) = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ↓reduceIte]
  rw [getLsbD_setSlice _ _ _ _ i hi]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, hi, BitVec.getLsbD_of_ge, Nat.le_of_not_gt h]

def validityBytes : List UInt8 :=
  [0x48,0x89,0x74,0x24,0x8,0xf,0xb6,0x44,0x24,0x8,0x24,0x1,0xf,0xb6,0xf8]

def validityEffect (s : RamState) : Effect :=
  let x := (Operand.reg 6 : Operand 64).read s
  let r := (x.setWidth 8 &&& 1).setWidth 64
  { rip := 0x112fa6
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), x⟩,
      ⟨(Operand.reg 0 : Operand 64), r⟩,
      ⟨(Operand.reg 7 : Operand 64), r⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem validity_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ComparePre 0x112f97)
      (codeRange 0x112f97 validityBytes) (Effect.post validityEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x112f97 0x48 (by unfold RexWPrefix; decide +kernel) 6
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 8#64) 8
      exact h.writable
    · change RangeApart (stackPtr s + 8#64) 8 0x112f97 5
      have ha := h.apart 0x12f97 5 (by decide +kernel)
      change RangeApart (stackPtr s + 8) 8 (0x112f97 : BitVec 64) 5 at ha
      exact ha
  case av =>
    intro s h
    apply h.avoids_code 0x12f97 validityBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f9c (by decide +kernel))
  advance_then (movzx_r32_m8_effect_step 0x112f9c 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x112f97 validityBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      change MemReadable s (stackPtr s + 8) 1
      exact ⟨by have h := hP.writable.readable.low; omega,
        fun i hi => hP.writable.readable.mem i (by omega)⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12fa1 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step 0x112fa1 1)
  case sub => exact codeRange_slice_subset 0x112f97 validityBytes 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.ByteOps.ByteOps.andAlImm8Effect_components ,
        Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12fa3 (by decide +kernel))
  advance_then (P256.Proofs.Common.Encoding.Parser.CompressedRoute.movzx_r32_al_effect_step 0x112fa3
    0xf8 rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f97 validityBytes 12 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [movzxAlEffect, Effect.components , Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12fa6 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [validityEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]
    simp [Operand.read, gprNumber, rexR, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      mergeGPR_byte_zeroExtend]
  · intro i
    cases i <;> x86_norm [validityEffect]
  · x86_norm [validityEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]

end P256.Proofs.Generate.Scalar
