import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Machine.Relocatable
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Reset.Header

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

inductive Layout where
  | reset
  | finalize
  | trait
  deriving DecidableEq

abbrev Layout.countSlot : Layout → Nat
  | .reset => 192
  | _ => 304

abbrev Layout.lengthSlot : Layout → Nat
  | .reset => 176
  | _ => 224

abbrev Layout.inputSlot : Layout → Nat
  | .reset => 168
  | _ => 216

abbrev Layout.size : Layout → Nat
  | .reset => 35
  | .finalize => 30
  | .trait => 27

def bytesAt (layout : Layout) : List UInt8 :=
  match layout with
  | .reset =>
    [0x4c, 0x89, 0x84, 0x24, 0xc0, 0, 0, 0, 0x49, 0x89, 0xcd,
     0x48, 0x89, 0x94, 0x24, 0xb0, 0, 0, 0, 0x49, 0x89, 0xf4,
     0x48, 0x89, 0xbc, 0x24, 0xa8, 0, 0, 0, 0x48, 0x8d, 0x44, 0x24, 0x40]
  | .finalize =>
    [0x4c, 0x89, 0x84, 0x24, 0x30, 1, 0, 0, 0x49, 0x89, 0xcd,
     0x48, 0x89, 0x94, 0x24, 0xe0, 0, 0, 0, 0x49, 0x89, 0xf7,
     0x48, 0x89, 0xbc, 0x24, 0xd8, 0, 0, 0]
  | .trait =>
    [0x4c, 0x89, 0x84, 0x24, 0x30, 1, 0, 0, 0x49, 0x89, 0xcc,
     0x48, 0x89, 0x94, 0x24, 0xe0, 0, 0, 0,
     0x48, 0x89, 0xbc, 0x24, 0xd8, 0, 0, 0]

structure PreAt (layout : Layout) (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  write192 : MemWritable s (rspOf s + BitVec.ofNat 64 layout.countSlot) 8
  apart192 : RangeApart (rspOf s + BitVec.ofNat 64 layout.countSlot) 8 p layout.size
  write176 : MemWritable s (rspOf s + BitVec.ofNat 64 layout.lengthSlot) 8
  apart176 : RangeApart (rspOf s + BitVec.ofNat 64 layout.lengthSlot) 8 p layout.size
  write168 : MemWritable s (rspOf s + BitVec.ofNat 64 layout.inputSlot) 8
  apart168 : RangeApart (rspOf s + BitVec.ofNat 64 layout.inputSlot) 8 p layout.size

def effectAt (layout : Layout) (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 layout.size
    writes := [
      ⟨(.mem (rspOf s + BitVec.ofNat 64 layout.countSlot) : Operand 64),
        (.reg 8 : Operand 64).read s⟩,
      ⟨(.reg (if layout = .trait then 12 else 13) : Operand 64),
        (.reg 1 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 layout.lengthSlot) : Operand 64),
        (.reg 2 : Operand 64).read s⟩] ++
      (match layout with
       | .trait => []
       | _ => [⟨(.reg (if layout = .reset then 12 else 15) : Operand 64),
                  (.reg 6 : Operand 64).read s⟩]) ++
      [⟨(.mem (rspOf s + BitVec.ofNat 64 layout.inputSlot) : Operand 64),
        (.reg 7 : Operand 64).read s⟩] ++
      (match layout with
       | .reset => [⟨(.reg 0 : Operand 64), rspOf s + 64⟩]
       | _ => []) }

def bytes := bytesAt .reset
abbrev Pre := PreAt .reset
def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 35
    writes := [
      ⟨(.mem (rspOf s + 192) : Operand 64), (.reg 8 : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), (.reg 1 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 176) : Operand 64), (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 12 : Operand 64), (.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 168) : Operand 64), (.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), rspOf s + 64⟩] }

set_option maxHeartbeats 800000 in
theorem runAt [Bindings] (layout : Layout) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytesAt layout).length) :
    AdvanceTriple boundary (PreAt layout p) (codeRange p (bytesAt layout))
      (Effect.post (effectAt layout p)) := by
  cases layout
  all_goals
    first
    | advance_reloc_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 0
        (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 8 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 0
        (.sib 4 none 0 (.d32 304)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 8 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
  all_goals
    first
    | advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x49 0xcd
        (by simp [RexWPrefix]) rfl)
        next (boundary_ne_program outside (inside 11 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x49 0xcc
        (by simp [RexWPrefix]) rfl)
        next (boundary_ne_program outside (inside 11 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
  all_goals
    first
    | advance_reloc_then (mov_m64_r64_effect_step (p + 11) 0x48 (by simp [RexWPrefix]) 2
        (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 19 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_then (mov_m64_r64_effect_step (p + 11) 0x48 (by simp [RexWPrefix]) 2
        (.sib 4 none 0 (.d32 224)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 19 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
  all_goals
    first
    | advance_reloc_then (mov_r64_r64_effect_step (p + 19) 0x49 0xf4
        (by simp [RexWPrefix]) rfl)
        next (boundary_ne_program outside (inside 22 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_then (mov_r64_r64_effect_step (p + 19) 0x49 0xf7
        (by simp [RexWPrefix]) rfl)
        next (boundary_ne_program outside (inside 22 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | skip
  all_goals
    first
    | advance_reloc_then (mov_m64_r64_effect_step (p + 22) 0x48 (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 30 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_then (mov_m64_r64_effect_step (p + 22) 0x48 (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 30 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | advance_reloc_then (mov_m64_r64_effect_step (p + 19) 0x48 (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 27 (by decide)))
  all_goals
    first
    | advance_reloc_then (lea_r64_effect_step (p + 30) 0x48 (by simp [RexWPrefix]) 0
        (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
        next (boundary_ne_program outside (inside 35 (by decide)))
      all_goals (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        unless t.isForall && t.bindingDomain!.getAppFn.isConstOf ``AdvanceTriple do
          throwError "instruction left an unsolved side condition")
    | skip
  all_goals
    apply AdvanceTriple.block_end
    intro s t _ h
    apply h.weaken
    · x86_norm [effectAt, Layout.size, Layout.countSlot, Layout.lengthSlot, Layout.inputSlot]
    · x86_norm [effectAt, Layout.size, Layout.countSlot, Layout.lengthSlot, Layout.inputSlot]
      repeat' constructor
      all_goals congr 2 <;> decide +kernel
    · intro i
      cases i <;> x86_norm [effectAt, Layout.size, Layout.countSlot, Layout.lengthSlot, Layout.inputSlot]
    · x86_norm [effectAt, Layout.size, Layout.countSlot, Layout.lengthSlot, Layout.inputSlot]

theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p bytes.length) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) :=
  runAt .reset p boundary outside inside

def Layout.offset : Layout → Wrapper.Variant → Nat
  | .reset, .sha224 => 0xd41
  | .reset, .sha256 => 0x2971
  | .finalize, .sha224 => 0x661
  | .finalize, .sha256 => 0x2271
  | .trait, .sha224 => 0x14e1
  | .trait, .sha256 => 0x3131

def Layout.pc (layout : Layout) (v : Wrapper.Variant) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (layout.offset v)

theorem code (layout : Layout) (v : Wrapper.Variant) {s : RamState}
    (loaded : ProgramLoaded s) : CodeIn (codeRange (layout.pc v) (bytesAt layout)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (layout.offset v) (bytesAt layout)
  · cases layout <;> cases v <;> decide +kernel
  · cases layout <;> cases v <;> decide +kernel

theorem inside (layout : Layout) (v : Wrapper.Variant) :
    BlockInProgram (layout.pc v) (bytesAt layout).length := by
  apply blockInProgram_of_textOffset
  cases layout <;> cases v <;> decide +kernel

theorem code_sha256 {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102971 bytes) s :=
  code .reset .sha256 loaded

theorem code_sha224 {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100d41 bytes) s :=
  code .reset .sha224 loaded

theorem inside_sha256 : BlockInProgram 0x102971 bytes.length :=
  inside .reset .sha256

theorem inside_sha224 : BlockInProgram 0x100d41 bytes.length :=
  inside .reset .sha224

end Sha2.Proofs.Reset.Header
