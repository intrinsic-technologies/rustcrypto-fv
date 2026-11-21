import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
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

namespace P256.Proofs.SignatureFromDer.Fixed.Finish.Checks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0x54,0x24,8,0xbe,4,0,0,0,0xb9,4,0,0,0]

def argumentEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 15#64
    writes := [⟨(.reg 2 : Operand 64), stackPtr s + 8#64⟩,
      ⟨(.reg 6 : Operand 64), 4⟩,
      ⟨(.reg 1 : Operand 64), 4⟩] }

theorem argument_correct [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (safe : ∀ k ∈ ([5#64,10#64,15#64] : List (BitVec 64)), p + k ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p argumentBytes)
      (Effect.post (argumentEffect p)) := by
  advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact safe 5 (by simp)
  advance_then (mov_r32_imm32_effect_step (p + 5) 0xbe (by decide +kernel) 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact safe 10 (by simp)
  advance_then (mov_r32_imm32_effect_step (p + 10) 0xb9 (by decide +kernel) 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact safe 15 (by simp)
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.SignatureFromDer.Fixed.Finish.Checks
