import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Parser.ByteStore
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
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Field (AdvanceTriple)

attribute [local x86_compose] gprNumber jmpEffect branchTarget

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1011c9
  writable : MemWritable s (rspOf s + 239) 1
  codeApart : RangeApart (rspOf s + 239) 1 0x1011c9 137

def bytes : List UInt8 :=
  [0x44,0x88,0xbc,0x24,0xef,0x0,0x0,0x0,0xeb,0x6d,0xba,0x40,0x0,0x0,0x0,0x4c,0x29,0xfa,0x4c,0x8d,0x2c,0x14,0x49,0x83,0xc5,0x8,0x4a,0x8d,0x3c,0x3c,0x48,0x81,0xc7,0xb0,0x0,0x0,0x0,0x49,0x83,0xc7,0xe0,0x48,0x8d,0x74,0x24,0x8,0x48,0x8d,0x2d,0x32,0xb7,0x1,0x0,0xff,0xd5,0x48,0xff,0x84,0x24,0x10,0x1,0x0,0x0,0x4c,0x8d,0xa4,0x24,0xb0,0x0,0x0,0x0,0xba,0x1,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6,0xe8,0x70,0x47,0x1,0x0,0x48,0xbe,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x4c,0x21,0xfe,0x4c,0x1,0xee,0x44,0x88,0xbc,0x24,0xef,0x0,0x0,0x0,0x4c,0x89,0xe7,0x4c,0x89,0xfa,0xff,0xd5,0x48,0x8d,0x7c,0x24,0x48,0x48,0x8d,0xb4,0x24,0xb0,0x0,0x0,0x0,0xb9,0xd,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x101252
    writes := [⟨(.mem (rspOf s + 239) : Operand 8), (.reg 15 : Operand 8).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 72⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 176⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

set_option maxRecDepth 2000 in
set_option maxHeartbeats 500000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1011c9 bytes) (Effect.post effect) := by
  advance_begin (Common.Instructions.mov_m8_r8_effect_step 0x1011c9 0x44
    (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl)
  case pre =>
    intro s hp
    refine ⟨hp.rip, hp.writable, ?_⟩
    intro i hi j hj
    change j < 8 at hj
    exact hp.codeApart i hi j (by omega)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.codeApart
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x11d1 (by decide))
  advance_then (jmp_rel8_effect_step 0x1011d1 0x6d (by decide))
  case sub => exact codeRange_slice_subset 0x1011c9 bytes 8 2
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), ?_, ?_⟩
    · exact jmpEffect_avoids _ _ _ _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1240 (by decide))
  advance_then (lea_r64_effect_step 0x101240 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1011c9 bytes 119 5
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1245 (by decide))
  advance_then (lea_r64_effect_step 0x101245 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1011c9 bytes 124 8
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x124d (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10124d 0xb9 (by decide) 13)
  case sub => exact codeRange_slice_subset 0x1011c9 bytes 132 5
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1252 (by decide))
  advance_finish [effect, gprNumber]

end P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Tail
