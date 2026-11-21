import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Memory
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad.LoadSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d735
  tailLength : MemReadable s (rspOf s + 191) 1
  blocks : MemReadable s (rspOf s + 224) 8

def bytes : List UInt8 :=
  [0x48,0x8d,0x9c,0x24,0xc0,0x0,0x0,0x0,0x44,0xf,0xb6,0xbc,0x24,0xbf,0x0,0x0,0x0,0x4c,0x8b,0xa4,0x24,0xe0,0x0,0x0,0x0,0x4d,0x89,0xfe,0x49,0x83,0xf6,0x3f]

def effect (s : RamState) : Effect :=
  { rip := 0x10d755
    writes := [⟨(.reg 3 : Operand 64), rspOf s + 192⟩,
      ⟨(.reg 15 : Operand 64), (memLoad s.external (rspOf s + 191) 8).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + 224) 64⟩,
      ⟨(.reg 14 : Operand 64), (memLoad s.external (rspOf s + 191) 8).setWidth 64 ^^^ 63⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d735 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd735 bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d735 bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (leaR64Effect 0x10d735 3 (.sib 4 none 0 (.d32 192))) from lea_r64_effect_step 0x10d735 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd73d (by decide))
  advance_then (show StepEffect _ _ (movzxR32M8Effect 0x10d73d 9 15 (.sib 4 none 0 (.d32 191))) from
    movzx_r_m8_rex_effect_step 0x10d73d 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
      (fun _ => rfl) 7 (.sib 4 none 0 (.d32 191)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d735 bytes 8 9
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      exact hP.tailLength
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd746 (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x10d746 12 (.sib 4 none 0 (.d32 224))) from
    mov_r64_m64_effect_step 0x10d746 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d32 224)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d735 bytes 17 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      exact hP.blocks
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd74e (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10d74e 14 15) from
    mov_r64_r64_effect_step 0x10d74e 0x4d 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d735 bytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd751 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR64Imm8Effect 0x10d751 14 63) from
      xor_r64_imm8_effect_step 0x10d751 0x49 0xf6 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10d735 bytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd755 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad.LoadSetup
