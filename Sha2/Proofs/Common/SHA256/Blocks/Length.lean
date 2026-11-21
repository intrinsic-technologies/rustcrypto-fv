import Sha2.Proofs.Wrapper.Hash.Padding.Length
import Sha2.Proofs.Common.Machine.Relocatable

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Length

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Instructions.ShiftLeft
open Sha2.Proofs.Common.Instructions.Or

inductive Registers where
  | r13_r12
  | r12_r15
  | r14_r12
  | r14_r15

def Registers.blocks : Registers → BitVec 5
  | .r13_r12 => 13
  | .r12_r15 => 12
  | .r14_r12 | .r14_r15 => 14

def Registers.tail : Registers → BitVec 5
  | .r13_r12 | .r14_r12 => 12
  | .r12_r15 | .r14_r15 => 15

def Registers.shiftBlocks : Registers → UInt8
  | .r13_r12 => 0xe5
  | .r12_r15 => 0xe4
  | .r14_r12 | .r14_r15 => 0xe6

def Registers.shiftTail : Registers → UInt8
  | .r13_r12 | .r14_r12 => 0xe4
  | .r12_r15 | .r14_r15 => 0xe7

def Registers.combine : Registers → UInt8
  | .r13_r12 => 0xec
  | .r12_r15 => 0xe7
  | .r14_r12 => 0xf4
  | .r14_r15 => 0xf7

def Registers.preShifted : Registers → Bool
  | .r13_r12 | .r12_r15 => false
  | .r14_r12 | .r14_r15 => true

def Registers.length (regs : Registers) : Nat := if regs.preShifted then 10 else 14

def bytes (regs : Registers) : List UInt8 :=
  (if regs.preShifted then [] else [0x49, 0xc1, regs.shiftBlocks, 9]) ++
    [0x41, 0xc1, regs.shiftTail, 3, 0x4d, 9, regs.combine] ++
    encodeBswapR64 (regs.tail.setWidth 4)

def effect (p : BitVec 64) (regs : Registers) (s : RamState) : Effect :=
  let blocks := if regs.preShifted then (.reg regs.blocks : Operand 64).read s
    else (.reg regs.blocks : Operand 64).read s <<< 9
  { rip := p + BitVec.ofNat 64 regs.length
    writes := (if regs.preShifted then [] else [⟨(.reg regs.blocks : Operand 64), blocks⟩]) ++
      [⟨(.reg regs.tail : Operand 64), bswap64
        (((.reg regs.tail : Operand 32).read s <<< 3).setWidth 64 ||| blocks)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64
attribute [local x86_local] Sha2.Proofs.Wrapper.Hash.Padding.Length.shift64_local
  Sha2.Proofs.Wrapper.Hash.Padding.Length.shift32_local

macro "sha256_length_steps " pref:num "," pc:term "," br:term "," tr:term "," sb:term "," st:term "," co:term "," outside:term "," inside:term : tactic => do
  let start := pref.getNat
  let shiftPc ← if start = 0 then pure pc else `($pc + $(Lean.quote start))
  let shiftStep ← `(StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR32Effect $shiftPc 4 $tr 3) from
      shl_r32_imm8_rex_effect_step $shiftPc 0x41 $st 3 (by simp [RexNoWPrefix]) rfl rfl)))
  let shiftNext ← `(boundary_ne_program $outside ($inside $(Lean.quote (start + 4)) (by decide)))
  let first ← if start = 0 then `(tactic| advance_reloc_begin $shiftStep next $shiftNext)
    else `(tactic| (
      advance_reloc_begin (StepEffect.forgetFlags (h :=
        (show StepEffect _ _ (shlR64Effect $pc 4 $br 9) from
          shl_r64_imm8_effect_step $pc 0x49 $sb 9 (by simp [RexWPrefix]) rfl rfl)))
        next (boundary_ne_program $outside ($inside 4 (by decide)))
      advance_reloc_then $shiftStep next $shiftNext))
  `(tactic| (
    $first:tactic
    advance_reloc_then (StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (orR64R64Effect ($pc + $(Lean.quote (start + 4))) $tr $br) from
        or_r64_r64_effect_step ($pc + $(Lean.quote (start + 4))) 0x4d $co (by simp [RexWPrefix]) rfl)))
      next (boundary_ne_program $outside ($inside $(Lean.quote (start + 7)) (by decide)))
    advance_reloc_then (bswap_r64_effect_step ($pc + $(Lean.quote (start + 7))) $tr)
      next (boundary_ne_program $outside ($inside $(Lean.quote (start + 10)) (by decide)))
    advance_finish [effect, Registers.blocks, Registers.tail, Registers.length, Registers.preShifted]))

theorem run [Bindings] (p : BitVec 64) (regs : Registers) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p regs.length) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytes regs)) (Effect.post (effect p regs)) := by
  cases regs with
  | r13_r12 => sha256_length_steps 4, p, 13, 12, 0xe5, 0xe4, 0xec, outside, inside
  | r12_r15 => sha256_length_steps 4, p, 12, 15, 0xe4, 0xe7, 0xe7, outside, inside
  | r14_r12 => sha256_length_steps 0, p, 14, 12, 0xe6, 0xe4, 0xf4, outside, inside
  | r14_r15 => sha256_length_steps 0, p, 14, 15, 0xe6, 0xe7, 0xf7, outside, inside

end Sha2.Proofs.Common.SHA256.Blocks.Length
