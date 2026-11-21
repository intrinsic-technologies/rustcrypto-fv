import Sha2.Proofs.Common.Machine.Epilogue
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine.Prologue

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

abbrev Layout := Epilogue.Layout

def registers (layout : Layout) : List (BitVec 5) :=
  (if layout.six then [5] else []) ++ [15,14,13,12,3]

def bytes (layout : Layout) : List UInt8 :=
  (if layout.six then [0x55] else []) ++
    [0x41,0x57,0x41,0x56,0x41,0x55,0x41,0x54,0x53,0x48,0x81,0xec] ++
    immBytes 32 (BitVec.ofNat 32 layout.allocation)

structure Pre (p : BitVec 64) (layout : Layout) (s : RamState) : Prop where
  rip : s.RIP = p
  write8 : MemWritable s (rspOf s + -8) 8
  write16 : MemWritable s (rspOf s + -16) 8
  write24 : MemWritable s (rspOf s + -24) 8
  write32 : MemWritable s (rspOf s + -32) 8
  write40 : MemWritable s (rspOf s + -40) 8
  write48 : if layout.six then MemWritable s (rspOf s + -48) 8 else True
  apart8 : RangeApart (rspOf s + -8) 8 p layout.length
  apart16 : RangeApart (rspOf s + -16) 8 p layout.length
  apart24 : RangeApart (rspOf s + -24) 8 p layout.length
  apart32 : RangeApart (rspOf s + -32) 8 p layout.length
  apart40 : RangeApart (rspOf s + -40) 8 p layout.length
  apart48 : if layout.six then RangeApart (rspOf s + -48) 8 p layout.length else True

def effect (p : BitVec 64) (layout : Layout) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 layout.length
    writes := (registers layout).zipIdx |>.map (fun (r,i) =>
      ⟨(.mem (rspOf s - BitVec.ofNat 64 (8*(i+1))) : Operand 64),
        (.reg r : Operand 64).read s⟩) |>.append
      [⟨(.reg 4 : Operand 64), rspOf s - BitVec.ofNat 64
        (layout.allocation + if layout.six then 48 else 40)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

attribute [local x86_compose] BitVec.sub_eq_add_neg pushAddr Epilogue.Layout.allocation Epilogue.Layout.six Epilogue.Layout.length

macro "sha256_prologue_steps " allocation:num "," count:num "," pc:term "," outside:term "," inside:term : tactic => do
  let regs := (if count.getNat = 6 then [5] else []) ++ [15,14,13,12,3]
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  let mut pos := 0
  for r in regs do
    let pcNow ← `($pc + $(Lean.quote pos))
    let effectStep ← if r < 8 then
      `(show StepEffect _ _ (pushR64Effect $pcNow 1 $(Lean.quote r)) from
        push_r64_effect_step $pcNow $(Lean.quote (0x50+r)) (by decide))
    else
      `(show StepEffect _ _ (pushR64Effect $pcNow 2 $(Lean.quote r)) from
        push_r64_rex_effect_step $pcNow 0x41 $(Lean.quote (0x50+r-8)) (by simp [RexPrefix]) (by decide))
    let first := pos = 0
    pos := pos + (if r < 8 then 1 else 2)
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $effectStep
      next (boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide))))
      else `(tactic| advance_reloc_then $effectStep
        next (boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))))
  let pcNow ← `($pc + $(Lean.quote pos))
  pos := pos + 7
  steps := steps.push (← `(tactic| advance_reloc_then
    (StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (subR64Imm32Effect $pcNow 4 $allocation) from
        sub_r64_imm32_effect_step $pcNow 0x48 0xec $allocation
          (by constructor <;> decide) (by decide) (by decide))))
    next (boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))))
  let mut result ← `(tactic| advance_finish [effect, registers, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, List.append, List.cons_append, List.nil_append, Epilogue.Layout.allocation,
    Epilogue.Layout.six, Epilogue.Layout.length])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

set_option maxHeartbeats 600000 in
set_option maxRecDepth 2000 in
theorem run [Bindings] (p : BitVec 64) (layout : Layout) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p layout.length) :
    AdvanceTriple boundary (Pre p layout) (codeRange p (bytes layout))
      (Effect.post (effect p layout)) := by
  cases layout with
  | five272 => sha256_prologue_steps 272, 5, p, outside, inside
  | six200 => sha256_prologue_steps 200, 6, p, outside, inside
  | six312 => sha256_prologue_steps 312, 6, p, outside, inside
  | six552 => sha256_prologue_steps 552, 6, p, outside, inside
  | six376 => sha256_prologue_steps 376, 6, p, outside, inside
  | six584 => sha256_prologue_steps 584, 6, p, outside, inside
  | six600 => sha256_prologue_steps 600, 6, p, outside, inside

end Sha2.Proofs.Common.Machine.Prologue
