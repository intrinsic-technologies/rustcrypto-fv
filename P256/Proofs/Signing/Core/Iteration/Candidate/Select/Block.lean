import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Select.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)


structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cb11
  readable : MemReadable s (rspOf s + 560) 4
  writable : ∀ offset ∈ ([176, 184, 192, 200] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([176, 184, 192, 200] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 73 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cb11 + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x84, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x44, 0x8b, 0xa4, 0x24, 0x30, 0x2, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x48, 0x8d, 0xb4, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xea, 0x44, 0x89, 0xe1]

def effect (s : RamState) : Effect :=
  { rip := 0x10cb5a
    writes := [
      ⟨(.mem (rspOf s + 200) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 192) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 184) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 176) : Operand 64), 0⟩,
      ⟨(.reg 12 : Operand 64), ((.mem (rspOf s + 560) : Operand 32).read s).setWidth 64⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 176⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rbp⟩,
      ⟨(.reg 1 : Operand 64), ((.mem (rspOf s + 560) : Operand 32).read s).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 73, (0x10cb11 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cb11 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10cb11 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 200 (by simp), hP.codeApart 200 (by simp) 0 12 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 200 (by simp) 0 73 (by decide)
  case next =>
    intro _ _
    exact outside 12 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb1d 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 192 (by simp)
    · x86_norm
      exact hP.codeApart 192 (by simp) 12 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 192 (by simp) 0 73 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb29 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 184 (by simp)
    · x86_norm
      exact hP.codeApart 184 (by simp) 24 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 184 (by simp) 0 73 (by decide)
    · exact outside 36 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb35 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 176 (by simp)
    · x86_norm
      exact hP.codeApart 176 (by simp) 36 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 176 (by simp) 0 73 (by decide)
    · exact outside 48 (by decide)
  advance_then (mov_r32_m32_effect_step 0x10cb41 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d32 560)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 56 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cb49 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 56 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 59 (by decide)
  advance_then (lea_r64_effect_step 0x10cb4c 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 59 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 67 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cb54 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 67 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 70 (by decide)
  advance_then (mov_r32_r32_rex_effect_step 0x10cb57 0x44 0xe1 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cb11 bytes 70 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 73 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    simp only [State.regValue, Operand.read, gprNumber, rexR, modrmReg, gprIndex, Syntax.Reg.fin]
    exact ⟨rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Candidate.Select.Block
