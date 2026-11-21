import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
import Sha2.Proofs.Wrapper512.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb.TailLength

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512
open Sha2.Proofs.Common.Instructions

def bytes (short : Bool) : List UInt8 :=
  [0x44,0x88,0xb4,0x24,0x4f,1,0,0] ++ if short then [0xeb,0x58] else []

def effect (p : BitVec 64) (short : Bool) (s : RamState) : Effect :=
  { rip := p + (if short then 98 else 8)
    writes := [⟨(.mem (rspOf s + 335) : Operand 8), (s.regValue .r14).setWidth 8⟩] }

structure Pre (p : BitVec 64) (short : Bool) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (rspOf s + 335) 1
  apart : RangeApart (rspOf s + 335) 1 p (bytes short).length

theorem code (v : Variant) (short : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (if short then 0xe1 else 0x127) .digest) (bytes short)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset .digest + if short then 0xe1 else 0x127)
  · cases short <;> cases v <;> decide +kernel
  · cases short <;> cases v <;> decide +kernel

theorem run [Bindings] (p : BitVec 64) (short : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes short).length)
    (target : InProgram (p + 98)) :
    AdvanceTriple boundary (Pre p short) (codeRange p (bytes short))
      (Effect.post (effect p short)) := by
  cases short with
  | false =>
    advance_reloc_begin (mov_m8_r8_effect_step p 0x44 (by simp [RexPrefix]) 6
      (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_finish [effect]
  | true =>
    have low : (branchTarget (p + 8) 2 ((88 : BitVec 8).signExtend 64)).toNat < 2^32 := by
      obtain ⟨byte, mem⟩ := target
      have bound := programSections_low.codeLow (_, byte) mem
      simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
    advance_reloc_begin (mov_m8_r8_effect_step p 0x44 (by simp [RexPrefix]) 6
      (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_reloc_then (jmp_rel8_effect_step (p + 8) 88 low)
      next (boundary_ne_program outside target)
    advance_finish [effect]

end Sha2.Proofs.Digest.Absorb.TailLength
