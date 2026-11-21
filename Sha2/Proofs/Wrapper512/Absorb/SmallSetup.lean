import Sha2.Proofs.Common.EffectCompose.AddImmediate
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.ResetLayout
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

def Variant.shortOffset (v : Variant) (form : Form := .slices) : Nat :=
  match form with
  | .slices | .digest => 0xf0
  | .reset stage =>
    if stage.val = 0 then 0x100 else if stage.val = 1 then 0x2b0 else
      match v with | .sha384 => 0x620 | .sha512 => 0x640 | _ => 0x600
  | .finalizeIntoReset false => 0xf0
  | .finalizeIntoReset true =>
    match v with | .sha384 => 0x460 | .sha512 => 0x480 | _ => 0x440
  | .traitFinalizeIntoReset false => 0x110
  | .traitFinalizeIntoReset true =>
    match v with | .sha384 => 0x4f0 | .sha512 => 0x510 | _ => 0x4d0

end Sha2.Proofs.Wrapper512

namespace Sha2.Proofs.Wrapper512.Absorb.SmallSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes (v : Variant := .sha384) (form : Form := .slices) : List UInt8 :=
  [if (v.traversal form).tailReg < 8 then 0x48 else 0x4a, 0x8d, 0x3c,
    UInt8.ofNat (4 + 8 * ((v.traversal form).tailReg % 8))] ++
  (match form with
  | .slices | .digest => [0x48,0x81,0xc7,0xf0,0,0,0]
  | .reset _ => []
  | .finalizeIntoReset _ => [0x48,0x83,0xc7,0x10]
  | .traitFinalizeIntoReset _ => [0x48,0x83,0xc7,0x20]) ++
  (if (v.traversal form).dataReg = 6 then [] else
    [if (v.traversal form).dataReg < 8 then 0x48 else 0x4c, 0x89,
     UInt8.ofNat (0xc6 + 8 * ((v.traversal form).dataReg % 8))]) ++
  [if (v.traversal form).lengthReg < 8 then 0x48 else 0x4c, 0x89,
   UInt8.ofNat (0xc2 + 8 * ((v.traversal form).lengthReg % 8))]

def effectAt (v : Variant) (form : Form) (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (bytes v form).length
    writes := [⟨(.reg 7 : Operand 64), rspOf s +
      ((Operand.reg (BitVec.ofNat 5 (v.traversal form).tailReg) : Operand 64).read s) +
        BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer)⟩] ++
      (if (v.traversal form).dataReg = 6 then [] else
        [⟨(.reg 6 : Operand 64), ((Operand.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64).read s)⟩]) ++
      [⟨(.reg 2 : Operand 64), ((Operand.reg (BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s)⟩]
    flags := if form.frameBytes = form.activeMemory.buffer then none else
      some (.ofStatusFlags (addSpec (rspOf s +
        ((Operand.reg (BitVec.ofNat 5 (v.traversal form).tailReg) : Operand 64).read s))
          (BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer))).2) }

def effect (v : Variant) (s : RamState) (form : Form := .slices) : Effect :=
  effectAt v form (v.pc (v.shortOffset form) form) s

theorem effect_result {v : Variant} {form : Form} {s t : RamState}
    (h : (effect v s form).Holds s t) :
    (Operand.reg 7 : Operand 64).read t = rspOf s +
      (Operand.reg (BitVec.ofNat 5 (v.traversal form).tailReg) : Operand 64).read s +
        BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer) ∧
    (Operand.reg 6 : Operand 64).read t =
      (Operand.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64).read s ∧
    (Operand.reg 2 : Operand 64).read t =
      (Operand.reg (BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s ∧
    AgreesExcept [.reg 7, .reg 6, .reg 2, .flags, .rip] s t := by
  have frame := h.agrees
  have writes := h.writes
  by_cases source : (v.traversal form).dataReg = 6
  · simp only [effect, effectAt, source, ↓reduceIte, List.append_nil,
      List.cons_append, List.nil_append, Write.AllHold] at writes
    refine ⟨writes.1, ?_, writes.2, frame.mono ?_⟩
    · rw [source]
      apply frame.read
      simp only [effect, effectAt, source, ↓reduceIte, Effect.components,
        List.append_nil, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, Write.component_reg]
      split <;> simp
    · intro c hc
      simp only [effect, effectAt, source, ↓reduceIte, Effect.components,
        List.append_nil, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, Write.component_reg] at hc
      split at hc <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false] <;> grind
  · simp only [effect, effectAt, source, ↓reduceIte, List.cons_append,
      List.nil_append, Write.AllHold] at writes
    refine ⟨writes.1, writes.2.1, writes.2.2, frame.mono ?_⟩
    intro c hc
    simp only [effect, effectAt, source, ↓reduceIte, Effect.components,
      List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, Write.component_reg] at hc
    split at hc <;> simp_all <;> grind

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s)
    (form : Form := .slices) (hd : form ≠ .digest := by decide) :
    CodeIn (codeRange (v.pc (v.shortOffset form) form) (bytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + v.shortOffset form) (bytes v form)
  all_goals cases v <;> cases form with
    | digest => contradiction
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | slices => decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem runAt [Bindings] (v : Variant) (form : Form) (p : BitVec 64)
    (boundary : ReturnBoundary) (safe : ∀ k ≤ 32, p + BitVec.ofNat 64 k ≠ boundary.rip) (hd : form ≠ .digest) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytes v form)) (Effect.post (effectAt v form p)) := by
  cases form with
  | digest => contradiction
  | slices =>
    cases v <;> (
    advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => intro _ _; exact safe 4 (by decide)
    advance_then (add_r64_imm32_effect_step (p + 4) 0x48 0xc7 240 (by simp [RexWPrefix]) rfl rfl)
    try (case sub => exact codeRange_slice_subset p _ 4 7)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      change (p + 4) + 7 ≠ boundary.rip
      rw [BitVec.add_assoc]
      exact safe 11 (by decide)
    advance_then (mov_r64_r64_effect_step (p + 11) 0x4c 0xee (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p _ 11 3)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      change (p + 11) + 3 ≠ boundary.rip
      rw [BitVec.add_assoc]
      exact safe 14 (by decide)
    advance_then (mov_r64_r64_effect_step (p + 14) 0x48 0xda (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p _ 14 3)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      change (p + 14) + 3 ≠ boundary.rip
      rw [BitVec.add_assoc]
      exact safe 17 (by decide)
    advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])
  | reset stage =>
    rcases stage with ⟨_ | _ | _ | n, h⟩
    · cases v <;> (
      simp only [bytes, Variant.traversal, ResetLayout.reset, List.getElem!_cons_zero]
      advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide +kernel) rfl rfl)
      case «next» => intro _ _; exact safe 4 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 4) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 4 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 4) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 7 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 7) 0x48 0xea (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 7 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 7) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 10 (by decide)
      advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])
    · cases v <;> (
      simp only [bytes, Variant.traversal, ResetLayout.reset, List.getElem!_cons_zero, List.getElem!_cons_succ]
      advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide +kernel) rfl rfl)
      case «next» => intro _ _; exact safe 4 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 4) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 4 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 4) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 7 (by decide)
      advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])
    · cases v <;> (
      simp only [bytes, Variant.traversal, ResetLayout.reset, List.getElem!_cons_zero, List.getElem!_cons_succ]
      advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide +kernel) rfl rfl)
      case «next» => intro _ _; exact safe 4 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 4) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 4 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 4) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 7 (by decide)
      advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])
    · omega
  | finalizeIntoReset second =>
    cases second
    · cases v with
      | sha384 | sha512 =>
        advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 15) 0 .none) (by decide +kernel) rfl rfl)
        case «next» => intro _ _; exact safe 4 (by decide)
        advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
        try (case sub => exact codeRange_slice_subset p _ 4 4)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 4) + 4 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xee (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 8 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 8) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 11 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 11) 0x48 0xea (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 11 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 11) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 14 (by decide)
        advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc]
      | sha512_224 | sha512_256 =>
        advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide +kernel) rfl rfl)
        case «next» => intro _ _; exact safe 4 (by decide)
        advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
        try (case sub => exact codeRange_slice_subset p _ 4 4)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 4) + 4 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xee (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 8 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 8) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 11 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 11) 0x48 0xea (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 11 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 11) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 14 (by decide)
        advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc]
    · cases v with
      | sha384 | sha512 =>
        advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 15) 0 .none) (by decide +kernel) rfl rfl)
        case «next» => intro _ _; exact safe 4 (by decide)
        advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
        try (case sub => exact codeRange_slice_subset p _ 4 4)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 4) + 4 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xea (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 8 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 8) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 11 (by decide)
        advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc]
      | sha512_224 | sha512_256 =>
        advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 3) 0 .none) (by decide +kernel) rfl rfl)
        case «next» => intro _ _; exact safe 4 (by decide)
        advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
        try (case sub => exact codeRange_slice_subset p _ 4 4)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 4) + 4 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 8 (by decide)
        advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xea (by simp [RexWPrefix]) rfl)
        try (case sub => exact codeRange_slice_subset p _ 8 3)
        case mid =>
          intro s t hp hh ho
          refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
          change (p + 8) + 3 ≠ boundary.rip
          rw [BitVec.add_assoc]
          exact safe 11 (by decide)
        advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc]
  | traitFinalizeIntoReset second =>
    cases second
    · cases v <;> (
      advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 3) 0 .none) (by decide +kernel) rfl rfl)
      case «next» => intro _ _; exact safe 4 (by decide)
      advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 32 (by simp [RexWPrefix]) rfl rfl)
      try (case sub => exact codeRange_slice_subset p _ 4 4)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 4) + 4 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 8 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 8) 0x48 0xee (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 8 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 8) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 11 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 11) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 11 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 11) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 14 (by decide)
      advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])
    · cases v <;> (
      advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 3) 0 .none) (by decide +kernel) rfl rfl)
      case «next» => intro _ _; exact safe 4 (by decide)
      advance_then (add_r64_imm8_effect_step (p + 4) 0x48 0xc7 32 (by simp [RexWPrefix]) rfl rfl)
      try (case sub => exact codeRange_slice_subset p _ 4 4)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 4) + 4 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 8 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xee (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 8 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 8) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 11 (by decide)
      advance_then (mov_r64_r64_effect_step (p + 11) 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
      try (case sub => exact codeRange_slice_subset p _ 11 3)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by rfl), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        change (p + 11) + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact safe 14 (by decide)
      advance_finish [effectAt, bytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Form.frameBytes, Form.activeMemory, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.add_zero, BitVec.shiftLeft_zero, BitVec.add_assoc])

theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (form : Form := .slices)
    (hd : form ≠ .digest := by decide) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (v.shortOffset form) form)
      (codeRange (v.pc (v.shortOffset form) form) (bytes v form))
      (Effect.post (fun s => effect v s form)) := by
  apply runAt (hd := hd)
  intro k hk
  apply boundary_ne_program outside
  rw [Variant.pc_add v (v.shortOffset form) k form]
  apply inProgram_of_textOffset
  have bound : v.textOffset form + v.shortOffset form + 32 < 71757 := by
    cases v <;> cases form with
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | _ => decide +kernel
  omega

end Sha2.Proofs.Wrapper512.Absorb.SmallSetup
