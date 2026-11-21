import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce.Blocks

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

attribute [local x86_compose] andAlImm8Effect

private theorem andAlLocal (p : BitVec 64) (imm : BitVec 8) :
    Effect.Local (andAlImm8Effect p imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andAlImm8Effect, h.read_reg]
  · intro s
    simp [andAlImm8Effect, Write.Full, Operand.Full]

attribute [local x86_local] andAlLocal

def argumentsBytes : List UInt8 :=
  [0xf, 0xb6, 0x44, 0x24, 0x48, 0x24, 0x1, 0x44, 0xf, 0xb6, 0xc0, 0x48, 0x8d, 0x6c, 0x24, 0x8, 0x48, 0x8d, 0x54, 0x24, 0x68, 0xbe, 0x4, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x48, 0x89, 0xef]

def argumentsEffect (s : RamState) : Effect :=
  let v0 := ((Operand.mem (stackPtr s + 72) : Operand 8).read s).setWidth 64
  let v1 := mergeGPR 8 ((v0).setWidth 8 &&& 1) (v0)
  let v2 := ((v1).setWidth 8).setWidth 64
  let v3 := (Operand.reg 4 : Operand 64).read s + 8
  let v4 := (Operand.reg 4 : Operand 64).read s + 104
  let v5 := (0x4 : BitVec 64)
  let v6 := (0x4 : BitVec 64)
  let v7 := v3
  { rip := 0x107b57
    writes := [⟨(.reg 0 : Operand 64), v1⟩,
      ⟨(.reg 1 : Operand 64), v6⟩,
      ⟨(.reg 2 : Operand 64), v4⟩,
      ⟨(.reg 5 : Operand 64), v3⟩,
      ⟨(.reg 6 : Operand 64), v5⟩,
      ⟨(.reg 7 : Operand 64), v7⟩,
      ⟨(.reg 8 : Operand 64), v2⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem arguments_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x107b35) (codeRange 0x107b35 argumentsBytes)
      (Effect.post argumentsEffect) := by
  advance_begin (movzx_r32_m8_effect_step 0x107b35 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    have h := (hP.writable 72 (by decide) (by decide)).readable
    refine ⟨hP.rip, ?_, fun i hi => h.mem i (by omega)⟩
    have := h.low
    change (stackPtr s + 72#64).toNat + 1 ≤ 2^32
    omega
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7b3a (by decide))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := (and_al_imm8_effect_step 0x107b3a 1)))
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 5 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 0, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b3c (by decide))⟩
  advance_then (movzx_r32_r8_rex_effect_step 0x107b3c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 7 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 8, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b40 (by decide))⟩
  advance_then (lea_r64_effect_step 0x107b40 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 11 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 5, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b45 (by decide))⟩
  advance_then (lea_r64_effect_step 0x107b45 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b4a (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x107b4a 0xbe (by decide) 4)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 21 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 6, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b4f (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x107b4f 0xb9 (by decide) 4)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 26 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 1, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b54 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x107b54 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x107b35 argumentsBytes 31 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 7, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _, boundary_ne_program outside (inProgram_of_textOffset 0x7b57 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [argumentsEffect, stackPtr, BitVec.xor_self, BitVec.zero_sub]
    all_goals simp [Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [argumentsEffect]
  · x86_norm [argumentsEffect, stackPtr]
    all_goals simp [Operand.read_reg64]

end P256.Proofs.Nonce.Initialize.Reduce.Blocks
