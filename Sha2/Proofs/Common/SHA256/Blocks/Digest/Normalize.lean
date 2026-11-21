import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Machine.Relocatable
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Digest.Normalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

def bytes : List UInt8 :=
  [0x4c,0x8d,0x74,0x24,64,0x44,0x0f,0xb6,0x64,0x24,63,0x4c,0x8b,0x6c,0x24,96]

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  tailReadable : MemReadable s (rspOf s + 63) 1
  counterReadable : MemReadable s (rspOf s + 96) 8

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 16
    writes := [⟨(.reg 14 : Operand 64), rspOf s + 64⟩,
      ⟨(.reg 12 : Operand 64), (memLoad s.external (rspOf s + 63) 8).setWidth 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 96) 64⟩] }

theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p bytes.length) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_reloc_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 5 (by decide)))
  advance_reloc_then (movzx_r32_m8_rex_effect_step (p + 5) 0x44
    (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 63)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (mov_r64_m64_effect_step (p + 11) 0x4c
    (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 16 (by decide)))
  advance_finish [effect, BitVec.setWidth_setWidth_of_le]

end Sha2.Proofs.Common.SHA256.Blocks.Digest.Normalize
