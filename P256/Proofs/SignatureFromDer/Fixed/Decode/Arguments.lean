import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
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
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,8, 0x48,0x8d,0x74,0x24,72, 0xba,32,0,0,0]

def argumentEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 15
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 2 : Operand 64), 32⟩] }

theorem arguments_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
    (offset : Nat) (bound : offset + 15 < 118431) :
    AdvanceTriple boundary (fun s => s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) argumentBytes)
      (Effect.post (argumentEffect (Extracted.textAddress + BitVec.ofNat 64 offset))) := by
  let p := Extracted.textAddress + BitVec.ofNat 64 offset
  have next (i : Nat) (hi : i ≤ 15) : p + BitVec.ofNat 64 i ≠ boundary.rip := by
    have h := boundary_ne_program hout (inProgram_of_textOffset (offset + i) (by omega))
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, p] using h
  advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact next 5 (by decide)
  advance_then (lea_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 5 + 5 ≠ boundary.rip
      simpa [BitVec.add_assoc] using next 10 (by decide)
  advance_then (mov_r32_imm32_effect_step (p + 10) 0xba (by decide +kernel) 32)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 10 + 5 ≠ boundary.rip
      simpa [BitVec.add_assoc] using next 15 (by decide)
  advance_finish [argumentEffect, stackPtr, Operand.read_reg64, p]

end P256.Proofs.SignatureFromDer.Fixed.Decode
