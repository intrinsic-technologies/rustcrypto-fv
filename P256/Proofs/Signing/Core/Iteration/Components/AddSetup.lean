import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.AddSetup

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Verifying.Core.Scalars (operand_write_mem_external operand_write_reg_external)

def Pre (s : RamState) : Prop := s.RIP = 0x10d2c2

def bytes : List UInt8 :=
  [0x48, 0x89, 0xef, 0x48, 0x8d, 0xb4, 0x24, 0x10, 0x5, 0x0, 0x0, 0x4c, 0x89, 0xfa]

def effect (s : RamState) : Effect :=
  { rip := 0x10d2d0
    writes := [
      ⟨(.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), rspOf s+1296⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 14, (0x10d2c2 : BitVec 64)+BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d2c2 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_r64_effect_step 0x10d2c2 0x48 0xef (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact outside 3 (by decide)
  advance_then (lea_r64_effect_step 0x10d2c5 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d2c2 bytes 3 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 11 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10d2cd 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d2c2 bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 14 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    all_goals simp [gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Components.AddSetup
