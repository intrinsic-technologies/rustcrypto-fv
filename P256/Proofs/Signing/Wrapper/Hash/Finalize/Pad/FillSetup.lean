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

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.FillSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions

attribute [local x86_compose] P256.Proofs.Common.Instructions.movM8Imm8RexEffect addR64Imm8Effect BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

attribute [local x86_local] P256.Proofs.Common.Instructions.movM8Imm8RexEffect_local



structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10287d
  writable : MemWritable s (rspOf s + (Operand.reg 3 : Operand 64).read s + 64) 1
  codeApart : RangeApart (rspOf s + (Operand.reg 3 : Operand 64).read s + 64) 1 0x10287d 18

def bytes : List UInt8 :=
  [0xc6,0x44,0x1c,0x40,0x80,0x48,0x8d,0x3c,0x1c,0x48,0x83,0xc7,0x41,0x31,0xf6,0x4c,0x89,0xe2]

def effect (s : RamState) : Effect :=
  { rip := 0x10288f
    writes := [⟨(.mem (rspOf s + (Operand.reg 3 : Operand 64).read s + 64) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg 3 : Operand 64).read s + 65⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10287d bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x287d bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10287d bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10287d
    (.sib 4 (some 3) 0 (.d8 64)) (by decide) rfl rfl 128)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h.writable
    · x86_norm
      intro i hi j hj
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h.codeApart i hi j (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h.codeApart
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x2882 (by decide))
  advance_then (show StepEffect _ _ (leaR64Effect 0x102882 7 (.sib 4 (some 3) 0 .none)) from
    lea_r64_effect_step 0x102882 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 (some 3) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10287d bytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2886 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (addR64Imm8Effect 0x102886 7 65) from
      add_r64_imm8_effect_step 0x102886 0x48 0xc7 65 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10287d bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, addR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x288a (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect 0x10288a 2 6 6) from
      xor_r32_r32_effect_step 0x10288a 0xf6 rfl)))
  case sub => exact codeRange_slice_subset 0x10287d bytes 13 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x288c (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10288c 2 12) from
    mov_r64_r64_effect_step 0x10288c 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10287d bytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x288f (by decide))
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.FillSetup
