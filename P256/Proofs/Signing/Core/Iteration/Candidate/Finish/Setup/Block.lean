import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cb5f
  writable : ∀ offset ∈ ([1328, 1336, 1344, 1352] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([1328, 1336, 1344, 1352] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 54 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cb5f + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x84, 0x24, 0x48, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x40, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x38, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x30, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def effect (s : RamState) : Effect :=
  { rip := 0x10cb95
    writes := [
      ⟨(.mem (rspOf s + 1352) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1344) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1336) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1328) : Operand 64), 0⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r15⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 54, (0x10cb5f : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cb5f bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10cb5f 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 1352 (by simp), hP.codeApart 1352 (by simp) 0 12 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 1352 (by simp) 0 54 (by decide)
  case next =>
    intro _ _
    exact outside 12 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb6b 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1344)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb5f bytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1344 (by simp)
    · x86_norm
      exact hP.codeApart 1344 (by simp) 12 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1344 (by simp) 0 54 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb77 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb5f bytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1336 (by simp)
    · x86_norm
      exact hP.codeApart 1336 (by simp) 24 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1336 (by simp) 0 54 (by decide)
    · exact outside 36 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cb83 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1328)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cb5f bytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1328 (by simp)
    · x86_norm
      exact hP.codeApart 1328 (by simp) 36 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1328 (by simp) 0 54 (by decide)
    · exact outside 48 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cb8f 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cb5f bytes 48 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, outside 51 (by decide)⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  advance_then (mov_r64_r64_effect_step 0x10cb92 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cb5f bytes 51 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, outside 54 (by decide)⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup.Block
