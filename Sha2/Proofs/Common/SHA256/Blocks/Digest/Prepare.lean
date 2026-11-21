import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Digest

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

namespace Header

def bytes : List UInt8 := [0x48,0x89,0xd3,0x49,0x89,0xf6,0x48,0x89,0xfe]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 9
    writes := [⟨(.reg 3 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 14 : Operand 64), s.regValue .rsi⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rdi⟩] }

theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p bytes.length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p bytes)
      (Effect.post (effect p)) := by
  advance_reloc_begin (mov_r64_r64_effect_step p 0x48 0xd3 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 3 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 3) 0x49 0xf6 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 6 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 6) 0x48 0xfe (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 9 (by decide)))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end Header

namespace CloneSetup

inductive Kind where
  | digest | finalizeLast | traitLast

def bytesFor : Kind → List UInt8
  | .digest => [0x48,0x89,0xe7,0x48,0x8d,0xb4,0x24,0xa8,0,0,0,0xb9,13,0,0,0]
  | .finalizeLast => [0x48,0x8d,0x7c,0x24,112,0x48,0x8d,0x74,0x24,8,0xb9,13,0,0,0]
  | .traitLast => [0x48,0x89,0xe7,0x48,0x8d,0x74,0x24,112,0xb9,13,0,0,0]

def Kind.source : Kind → BitVec 64
  | .digest => 168 | .finalizeLast => 8 | .traitLast => 112

def Kind.destination : Kind → BitVec 64
  | .digest => 0 | .finalizeLast => 112 | .traitLast => 0

def effectFor (k : Kind) (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (bytesFor k).length
    writes := [⟨(.reg 7 : Operand 64), rspOf s + k.destination⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + k.source⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

def bytes : List UInt8 := bytesFor .digest

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 16
    writes := [⟨(.reg 7 : Operand 64), rspOf s⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 168⟩,
      ⟨(.reg 1 : Operand 64), 13⟩] }

theorem runFor [Bindings] (k : Kind) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytesFor k).length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (bytesFor k))
      (Effect.post (effectFor k p)) := by
  cases k with
  | digest =>
    advance_reloc_begin (mov_r64_r64_effect_step p 0x48 0xe7 (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 3 (by decide)))
    advance_reloc_then (lea_r64_effect_step (p + 3) 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 11 (by decide)))
    advance_reloc_then (mov_r32_imm32_effect_step (p + 11) 0xb9 (by decide) 13)
      next (boundary_ne_program outside (inside 16 (by decide)))
    advance_finish [effectFor, bytesFor, Kind.source, Kind.destination, BitVec.add_zero]
  | finalizeLast =>
    advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 5 (by decide)))
    advance_reloc_then (lea_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 10 (by decide)))
    advance_reloc_then (mov_r32_imm32_effect_step (p + 10) 0xb9 (by decide) 13)
      next (boundary_ne_program outside (inside 15 (by decide)))
    advance_finish [effectFor, bytesFor, Kind.source, Kind.destination, BitVec.add_zero]
  | traitLast =>
    advance_reloc_begin (mov_r64_r64_effect_step p 0x48 0xe7 (by simp [RexWPrefix]) rfl)
      next (boundary_ne_program outside (inside 3 (by decide)))
    advance_reloc_then (lea_r64_effect_step (p + 3) 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
      next (boundary_ne_program outside (inside 8 (by decide)))
    advance_reloc_then (mov_r32_imm32_effect_step (p + 8) 0xb9 (by decide) 13)
      next (boundary_ne_program outside (inside 13 (by decide)))
    advance_finish [effectFor, bytesFor, Kind.source, Kind.destination, BitVec.add_zero]

theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p bytes.length) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p bytes)
      (Effect.post (effect p)) := by
  have he : effectFor .digest p = effect p := by
    funext s
    simp [effectFor, effect, Kind.source, Kind.destination, bytesFor]
  rw [← he]
  exact runFor .digest p boundary outside inside

end CloneSetup

end Sha2.Proofs.Common.SHA256.Blocks.Digest
