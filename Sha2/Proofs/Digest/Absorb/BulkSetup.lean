import Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
import Sha2.Proofs.Common.Instructions.CrossPageStore.Immediate
import Sha2.Proofs.Wrapper512.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb.BulkSetup

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512
open Sha2.Proofs.Common.Instructions

def bytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x50,1,0,0,0x4c,0x89,0xf2,0x48,0xc1,0xea,7,
    0x49,0xbf,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x4d,0x21,0xf7,
    0x41,0x83,0xe6,0x7f,0x49,1,0xf7,0x48,0x89,0x94,0x24,0x90,1,0,0,
    0x48,0xc7,0x84,0x24,0x98,1,0,0,0,0,0,0]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 55
    writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 336⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r14 >>> 7⟩,
      ⟨(.reg 15 : Operand 64), s.regValue .rsi + (s.regValue .r14 &&& 0x7fffffffffffff80)⟩,
      ⟨(.reg 14 : Operand 64), ((s.regValue .r14).setWidth 32 &&& 127).setWidth 64⟩,
      ⟨(.mem (rspOf s + 400) : Operand 64), s.regValue .r14 >>> 7⟩,
      ⟨(.mem (rspOf s + 408) : Operand 64), 0⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : CrossPageStore.Writable s (rspOf s + 400) 8
  highWritable : CrossPageStore.Writable s (rspOf s + 408) 8
  apart : RangeApart (rspOf s + 400) 8 p bytes.length
  highApart : RangeApart (rspOf s + 408) 8 p bytes.length

theorem code (v : Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xeb .digest) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset .digest + 0xeb)
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

set_option maxHeartbeats 600000 in
theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p bytes.length) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes)
      (Effect.post (effect p)) := by
  advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := shr_r64_imm8_effect_step
    (p + 11) 0x48 0xea 7 (by simp [RexWPrefix]) rfl rfl))
    next (boundary_ne_program outside (inside 15 (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step (p + 15) 0x49 0xbf
    (by simp [RexWPrefix]) (by decide) 0x7fffffffffffff80)
    next (boundary_ne_program outside (inside 25 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := and_r64_r64_effect_step
    (p + 25) 0x4d 0xf7 (by simp [RexWPrefix]) rfl))
    next (boundary_ne_program outside (inside 28 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := and_r32_imm8_rex_effect_step
    (p + 28) 0x41 0xe6 127 (by simp [RexNoWPrefix]) rfl rfl))
    next (boundary_ne_program outside (inside 32 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := add_r64_r64_effect_step
    (p + 32) 0x49 0xf7 (by simp [RexWPrefix]) rfl))
    next (boundary_ne_program outside (inside 35 (by decide)))
  advance_reloc_then (CrossPageStore.mov_m64_r64_effect_step_any (p + 35) 0x48
    (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 43 (by decide)))
  advance_reloc_then (CrossPageStore.mov_m64_imm32_effect_step_any (p + 43) 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 408)) (by decide) rfl rfl 0)
    next (boundary_ne_program outside (inside 55 (by decide)))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    refine ⟨rfl, ?_, rfl, rfl⟩
    exact (BitVec.add_comm _ _).trans (congrArg (· + _) (BitVec.and_comm _ _))
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]


end Sha2.Proofs.Digest.Absorb.BulkSetup
