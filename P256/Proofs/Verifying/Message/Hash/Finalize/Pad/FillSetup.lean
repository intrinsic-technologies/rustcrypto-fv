import P256.Proofs.Common.Instructions.StoreByte
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
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
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad.FillSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions

attribute [local x86_compose] P256.Proofs.Common.Instructions.movM8Imm8RexEffect incR64Effect BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

attribute [local x86_local] P256.Proofs.Common.Instructions.movM8Imm8RexEffect_local



structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d755
  writable : MemWritable s (rspOf s + (Operand.reg 15 : Operand 64).read s + 128) 1
  codeApart : RangeApart (rspOf s + (Operand.reg 15 : Operand 64).read s + 128) 1 0x10d755 25

def bytes : List UInt8 :=
  [0x42,0xc6,0x84,0x3c,0x80,0x0,0x0,0x0,0x80,0x4a,0x8d,0x3c,0x3c,0x48,0x81,0xc7,0x81,0x0,0x0,0x0,0x31,0xf6,0x4c,0x89,0xf2]

def effect (s : RamState) : Effect :=
  { rip := 0x10d76e
    writes := [⟨(.mem (rspOf s + (Operand.reg 15 : Operand 64).read s + 128) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg 15 : Operand 64).read s + 129⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d755 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd755 bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d755 bytes) (Effect.post effect) := by
  advance_begin (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x10d755 0x42 (by simp [RexNoWPrefix])
    (.sib 4 (some 15) 0 (.d32 128)) (by decide) rfl rfl 128)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read_reg64, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h.writable
    · x86_norm
      intro i hi j hj
      simpa only [rspOf, Operand.read_reg64, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h.codeApart i hi j (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa only [rspOf, Operand.read_reg64, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h.codeApart
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd75e (by decide))
  advance_then (show StepEffect _ _ (leaR64Effect 0x10d75e 7 (.sib 4 (some 15) 0 .none)) from
    lea_r64_effect_step 0x10d75e 0x4a (by simp [RexWPrefix]) 7
      (.sib 4 (some 15) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d755 bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd762 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    add_r64_imm32_effect_step 0x10d762 0x48 0xc7 129 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10d755 bytes 13 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, addR64Imm32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd769 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect 0x10d769 2 6 6) from
      xor_r32_r32_effect_step 0x10d769 0xf6 rfl)))
  case sub => exact codeRange_slice_subset 0x10d755 bytes 20 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd76b (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10d76b 2 14) from
    mov_r64_r64_effect_step 0x10d76b 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d755 bytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd76e (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad.FillSetup
