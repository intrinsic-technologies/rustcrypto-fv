import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Wrapper.Hash.Padding.Length
import Sha2.Proofs.Common.SHA256.Instances.Finalize
import Sha2.Proofs.Common.SHA256.Finalize.State
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Reset.Normalize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.ShiftLeft

attribute [local x86_compose] shlR64Effect
attribute [local x86_local] Sha2.Proofs.Wrapper.Hash.Padding.Length.shift64_local

inductive Form where
  | reset
  | finalize
  | trait
  deriving DecidableEq

def Form.frameBytes : Form → Nat
  | .reset => 248
  | .finalize | .trait => 360

def Form.reserve : Form → Nat
  | .reset => 720
  | .finalize | .trait => 832

def bytes (first : Bool) (form : Form := .reset) : List UInt8 :=
  match form, first with
  | .reset, true => [0xf, 0xb6, 0x44, 0x24, 0x3f, 0x4c, 0x8b, 0x74, 0x24, 0x60, 0x49, 0xc1, 0xe6, 0x9, 0x4c, 0x8b, 0xac, 0x24, 0xb8, 0x0, 0x0, 0x0, 0xeb, 0x14, 0x48, 0x89, 0x48, 0x18, 0x48, 0x89, 0x50, 0x10, 0x48, 0x89, 0x70, 0x8, 0x48, 0x89, 0x38, 0x45, 0x31, 0xf6, 0x31, 0xc0, 0x44, 0xf, 0xb6, 0xf8]
  | .reset, false => [0xf, 0xb6, 0x44, 0x24, 0x3f, 0x4c, 0x8b, 0x74, 0x24, 0x60, 0x49, 0xc1, 0xe6, 0x9, 0xeb, 0x5, 0x45, 0x31, 0xf6, 0x31, 0xc0, 0x44, 0xf, 0xb6, 0xf8]
  | .finalize, true => [0xf, 0xb6, 0x44, 0x24, 0x47, 0x4c, 0x8b, 0x74, 0x24, 0x68, 0x49, 0xc1, 0xe6, 0x9, 0x4c, 0x8b, 0xac, 0x24, 0x28, 0x1, 0x0, 0x0, 0xeb, 0x5, 0x45, 0x31, 0xf6, 0x31, 0xc0, 0x44, 0xf, 0xb6, 0xe0]
  | .finalize, false => [0x48, 0x8d, 0x9c, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0xaf, 0x0, 0x0, 0x0, 0x4c, 0x8b, 0xa4, 0x24, 0xd0, 0x0, 0x0, 0x0]
  | .trait, true => [0xf, 0xb6, 0x84, 0x24, 0xaf, 0x0, 0x0, 0x0, 0x4c, 0x8b, 0xb4, 0x24, 0xd0, 0x0, 0x0, 0x0, 0x49, 0xc1, 0xe6, 0x9, 0x4c, 0x8b, 0xa4, 0x24, 0x28, 0x1, 0x0, 0x0, 0xeb, 0x5, 0x45, 0x31, 0xf6, 0x31, 0xc0, 0x48, 0x8d, 0xac, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xf8]
  | .trait, false => [0x48, 0x8d, 0x5c, 0x24, 0x40, 0x44, 0xf, 0xb6, 0x7c, 0x24, 0x3f, 0x4c, 0x8b, 0x64, 0x24, 0x60]

def length (first : Bool) (form : Form := .reset) : Nat :=
  match form with
  | .reset => if first then 48 else 25
  | .finalize => if first then 33 else 25
  | .trait => if first then 47 else 16

def entryOffset (first : Bool) (v : Wrapper.Variant) (form : Form := .reset) : Nat :=
  match form, first, v with
  | .reset, true, .sha256 => 0x2c26
  | .reset, true, .sha224 => 0xff6
  | .reset, false, .sha256 => 0x2f36
  | .reset, false, .sha224 => 0x12f6
  | .finalize, true, .sha256 => 0x23e7
  | .finalize, true, .sha224 => 0x7d7
  | .finalize, false, .sha256 => 0x271a
  | .finalize, false, .sha224 => 0xafa
  | .trait, true, .sha256 => 0x32df
  | .trait, true, .sha224 => 0x168f
  | .trait, false, .sha256 => 0x366e
  | .trait, false, .sha224 => 0x1a0e

def entry (first : Bool) (v : Wrapper.Variant) (form : Form := .reset) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (entryOffset first v form)

def finalization (first : Bool) (form : Form := .reset) : Finalization :=
  match form, first with
  | .reset, true => .resetFirst
  | .reset, false => .resetLast
  | .finalize, true => .finalizeFirst
  | .finalize, false => .finalizeLast
  | .trait, true => .traitFirst
  | .trait, false => .traitLast

def bufferOffset (first : Bool) (form : Form := .reset) : Nat :=
  (finalization first form).variant.buffer.value

def outputSlot (form : Form := .reset) : Nat := if form = .reset then 184 else 296

def outputReg (form : Form := .reset) : BitVec 5 := if form = .trait then 12 else 13

def tailReg (first : Bool) (form : Form := .reset) : BitVec 5 :=
  (finalization first form).variant.registers.tail

def shifted (first : Bool) (form : Form := .reset) : Bool := first || form == .reset

structure Pre (p : BitVec 64) (first : Bool) (s : RamState)
    (form : Form := .reset) : Prop where
  rip : s.RIP = p
  tailReadable : MemReadable s (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 63)) 1
  counterReadable : MemReadable s (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 96)) 8
  outputReadable : if first then MemReadable s (rspOf s + BitVec.ofNat 64 (outputSlot form)) 8 else True

def effect (p : BitVec 64) (first : Bool) (s : RamState) (form : Form := .reset) : Effect :=
  match form with
  | .reset =>
    { rip := p + BitVec.ofNat 64 (length first)
      writes := [⟨(.reg 0 : Operand 64), (memLoad s.external (rspOf s + 63) 8).setWidth 64⟩,
        ⟨(.reg 14 : Operand 64), memLoad s.external (rspOf s + 96) 64 <<< 9⟩] ++
        (if first then [⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 184) 64⟩] else []) ++
        [⟨(.reg 15 : Operand 64), (memLoad s.external (rspOf s + 63) 8).setWidth 64⟩]
      flags := some ⟨none, none, none, none, none, none⟩ }
  | .finalize | .trait =>
    let tail := (memLoad s.external (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 63)) 8).setWidth 64
    let count := memLoad s.external (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 96)) 64
    { rip := p + BitVec.ofNat 64 (length first form)
      writes := (if shifted first form then
        [⟨(.reg 0 : Operand 64), tail⟩, ⟨(.reg 14 : Operand 64), count <<< 9⟩] else
        [⟨(.reg 3 : Operand 64), rspOf s + BitVec.ofNat 64 (bufferOffset first form + 64)⟩]) ++
        (if first then [⟨(.reg (outputReg form) : Operand 64),
          memLoad s.external (rspOf s + BitVec.ofNat 64 (outputSlot form)) 64⟩] else []) ++
        (if first && form == .trait then
          [⟨(.reg 5 : Operand 64), rspOf s + 176⟩] else []) ++
        [⟨(.reg (tailReg first form) : Operand 64), tail⟩] ++
        (if shifted first form then [] else [⟨(.reg 12 : Operand 64), count⟩])
      flags := if shifted first form then some ⟨none, none, none, none, none, none⟩ else none }

macro "reset_normalize_steps " kind:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let k := kind.getId.toString
  let isFirst := k != "last"
  let trait := k == "trait"
  let fin := k == "finalize"
  let tail := if trait then 175 else if fin then 71 else 63
  let count := tail + 33
  let loadLen := if trait then 8 else 5
  let shiftPos := 2 * loadLen
  let afterShift := shiftPos + 4
  let jumpPos := afterShift + if isFirst then 8 else 0
  let target := jumpPos + 2 + if k == "first" then 20 else 5
  let size := target + (if trait then 8 else 0) + 4
  let displacement := if k == "first" then 20 else 5
  let tailDisp ← if trait then `(Disp.d32 $(Lean.quote tail)) else `(Disp.d8 $(Lean.quote tail))
  let countDisp ← if trait then `(Disp.d32 $(Lean.quote count)) else `(Disp.d8 $(Lean.quote count))
  let extra ← if isFirst then `(tactic| (
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote afterShift)) 0x4c
      (by simp [RexWPrefix]) $(Lean.quote (if trait then 4 else 5))
      (.sib 4 none 0 (.d32 $(Lean.quote (if k == "first" then 184 else 296)))) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote jumpPos) (by decide)))))
    else `(tactic| skip)
  let pointer ← if trait then `(tactic| (
    advance_reloc_then (lea_r64_effect_step ($pc + $(Lean.quote target)) 0x48
      (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote (target+8)) (by decide)))))
    else `(tactic| skip)
  `(tactic| (
    have low : (branchTarget ($pc + $(Lean.quote jumpPos)) 2
        (($(Lean.quote displacement) : BitVec 8).signExtend 64)).toNat < 2^32 := by
      obtain ⟨byte, mem⟩ := $inside $(Lean.quote target) (by decide)
      have bound := programSections_low.codeLow (_, byte) mem
      simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
    advance_reloc_begin (movzx_r32_m8_effect_step $pc 0
      (.sib 4 none 0 $tailDisp) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote loadLen) (by decide)))
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote loadLen)) 0x4c
      (by simp [RexWPrefix]) 6 (.sib 4 none 0 $countDisp) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote shiftPos) (by decide)))
    advance_reloc_then (StepEffect.forgetFlags (h :=
      (show StepEffect _ _ (shlR64Effect ($pc + $(Lean.quote shiftPos)) 4 14 9) from
        shl_r64_imm8_effect_step ($pc + $(Lean.quote shiftPos)) 0x49 0xe6 9
          (by simp [RexWPrefix]) rfl rfl)))
      next (boundary_ne_program $outside ($inside $(Lean.quote afterShift) (by decide)))
    $extra:tactic
    advance_reloc_then (jmp_rel8_effect_step ($pc + $(Lean.quote jumpPos))
      $(Lean.quote displacement) low)
      next (boundary_ne_program $outside ($inside $(Lean.quote target) (by decide)))
    $pointer:tactic
    advance_reloc_then (movzx_r32_r8_rex_effect_step ($pc + $(Lean.quote (size-4)))
      0x44 (by simp [RexNoWPrefix]) $(Lean.quote (if fin then 0xe0 else 0xf8)) rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote size) (by decide)))
    advance_finish [effect, length, bytes, bufferOffset, finalization, outputSlot, outputReg,
      tailReg, shifted, Finalization.variant, Finalize.Variant.buffer, Blocks.Zero.Offset.value,
      BitVec.setWidth_setWidth_of_le]))

macro "reset_normalize_last " kind:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let fin := kind.getId == `finalize
  let leaLen := if fin then 8 else 5
  let tailLen := if fin then 9 else 6
  let countLen := if fin then 8 else 5
  let hd ← if fin then `(Disp.d32 176) else `(Disp.d8 64)
  let td ← if fin then `(Disp.d32 175) else `(Disp.d8 63)
  let cd ← if fin then `(Disp.d32 208) else `(Disp.d8 96)
  `(tactic| (
    advance_reloc_begin (lea_r64_effect_step $pc 0x48 (by simp [RexWPrefix]) 3
      (.sib 4 none 0 $hd) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote leaLen) (by decide)))
    advance_reloc_then (movzx_r32_m8_rex_effect_step ($pc + $(Lean.quote leaLen))
      0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 $td) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote (leaLen+tailLen)) (by decide)))
    advance_reloc_then (mov_r64_m64_effect_step ($pc + $(Lean.quote (leaLen+tailLen)))
      0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 $cd) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote (leaLen+tailLen+countLen)) (by decide)))
    advance_finish [effect, length, bytes, bufferOffset, finalization, outputSlot, outputReg,
      tailReg, shifted, Finalization.variant, Finalize.Variant.buffer, Blocks.Zero.Offset.value,
      BitVec.setWidth_setWidth_of_le]))

theorem run [Bindings] (p : BitVec 64) (first : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) {form : Form}
    (inside : BlockInProgram p (length first form)) :
    AdvanceTriple boundary (fun s => Pre p first s form) (codeRange p (bytes first form))
      (Effect.post (fun s => effect p first s form)) := by
  cases form <;> cases first
  · reset_normalize_steps last, p, outside, inside
  · reset_normalize_steps first, p, outside, inside
  · reset_normalize_last finalize, p, outside, inside
  · reset_normalize_steps finalize, p, outside, inside
  · reset_normalize_last trait, p, outside, inside
  · reset_normalize_steps trait, p, outside, inside

theorem code (first : Bool) (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s)
    (form : Form := .reset) :
    CodeIn (codeRange (entry first v form) (bytes first form)) s :=
  programText_slice (programLoaded_codeIn loaded) (entryOffset first v form) (bytes first form)
    (by cases form <;> cases v <;> cases first <;> decide +kernel)
    (by cases form <;> cases v <;> cases first <;> decide +kernel)

theorem inside (first : Bool) (v : Wrapper.Variant) (form : Form := .reset) :
    BlockInProgram (entry first v form) (length first form) :=
  blockInProgram_of_textOffset (entryOffset first v form) (length first form)
    (by cases form <;> cases v <;> cases first <;> decide +kernel)

theorem memory {p : BitVec 64} {first : Bool} {s t : RamState} {form : Form}
    (result : (effect p first s form).Holds s t) : t.external = s.external := by
  apply result.agrees.external
  cases form <;> cases first <;> simp [effect, Effect.components, Component.Covers,
    shifted, tailReg, outputReg]

theorem prepared {s t : RamState} {message : ByteArray} {v : Wrapper.Variant}
    (first : Bool) {form : Form}
    (hasher : HasherAt s (rspOf s + BitVec.ofNat 64 (bufferOffset first form)) message v.initialHash)
    (result : (effect (entry first v form) first s form).Holds s t) :
    Finalize.Prepared ((finalization first form).layout v) (rspOf s) message t := by
  have nextPC : entry first v form + BitVec.ofNat 64 (length first form) =
      ((finalization first form).layout v).entry := by
    cases form <;> cases v <;> cases first <;> decide +kernel
  have tailValue : (memLoad s.external
      (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 63)) 8).setWidth 64 =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, memLoad_8]
    change ((s.external[rspOf s + BitVec.ofNat 64 (bufferOffset first form) + 63]?).getD 0).toBitVec.setWidth 64 = _
    rw [hasher.tailLength]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt8.toNat_ofNat', BitVec.toNat_ofNat]
    have bound := Nat.mod_lt message.size (by decide : 0 < 64)
    omega
  have blocks : memLoad s.external (rspOf s + BitVec.ofNat 64 (bufferOffset first form + 96)) 64 =
      BitVec.ofNat 64 (message.size / 64) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hasher.blocks
  refine ⟨by cases form <;> exact result.rip.trans nextPC, ?_, ?_, ?_, ?_, ?_⟩
  · apply result.agrees.read (n := 64) (r := 4)
    cases form <;> cases first <;> simp [effect, Effect.components, shifted, tailReg, outputReg, finalization, Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail]
  · have hashVariant : ((finalization first form).layout v).hashVariant = v := by
      cases form <;> cases first <;> rfl
    rw [hashVariant]
    exact hasher.of_bytes (fun i _ => congrArg (fun m => m[_]?) (memory result))
  · have w := result.writes
    cases form <;> cases first <;>
      simp_all [effect, shifted, tailReg, outputReg, bufferOffset, finalization,
        Write.AllHold, Operand.read, Finalization.layout, Finalization.variant,
        Finalize.Variant.buffer, Blocks.Zero.Offset.value, Finalize.Variant.registers,
        Blocks.Length.Registers.tail]
  · have w := result.writes
    cases form <;> cases first <;>
      simp_all [effect, shifted, tailReg, outputReg, bufferOffset, finalization,
        Finalize.countValue, Finalize.Variant.registers, Blocks.Length.Registers.preShifted, Write.AllHold, Operand.read, Finalization.layout, Finalization.variant,
        Finalize.Variant.buffer, Blocks.Zero.Offset.value, Finalize.Variant.registers,
        Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks]
  · have w := result.writes
    cases form <;> cases first <;>
      simp_all [effect, shifted, tailReg, outputReg, bufferOffset, finalization,
        Finalize.Variant.needsHashPointer, Finalize.Layout.hash, Finalize.Layout.buffer, Write.AllHold, Operand.read, Finalization.layout, Finalization.variant,
        Finalize.Variant.buffer, Blocks.Zero.Offset.value, Finalize.Variant.registers,
        Blocks.Length.Registers.tail, Finalize.Variant.hashReg,
        BitVec.add_assoc]

theorem restored_output {p : BitVec 64} {s t : RamState} {form : Form}
    (result : (effect p true s form).Holds s t) :
    (.reg (outputReg form) : Operand 64).read t =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (outputSlot form)) 64 := by
  cases form <;> exact result.writes.2.2.1

def emptyLength (form : Form) : Nat := if form = .trait then 17 else 9

def emptyBytes (form : Form) : List UInt8 :=
  [0x45, 0x31, 0xf6, 0x31, 0xc0] ++
    (if form = .trait then [0x48, 0x8d, 0xac, 0x24, 0xb0, 0, 0, 0] else []) ++
    [0x44, 0x0f, 0xb6, if form = .finalize then 0xe0 else 0xf8]

def emptyEntry (v : Wrapper.Variant) (form : Form) : BitVec 64 :=
  entry true v form + BitVec.ofNat 64 (length true form - emptyLength form)

def emptyEffect (p : BitVec 64) (form : Form) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (emptyLength form)
    writes := [⟨(.reg 14 : Operand 64), 0⟩, ⟨(.reg 0 : Operand 64), 0⟩] ++
      (if form = .trait then [⟨(.reg 5 : Operand 64), rspOf s + 176⟩] else []) ++
      [⟨(.reg (tailReg true form) : Operand 64), 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

macro "reset_normalize_empty " kind:ident "," pc:term "," outside:term "," inside:term : tactic => do
  let trait := kind.getId == `trait
  let fin := kind.getId == `finalize
  let extra ← if trait then `(tactic| (
    advance_reloc_then (lea_r64_effect_step ($pc + 5) 0x48 (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
      next (boundary_ne_program $outside ($inside 13 (by decide)))))
    else `(tactic| skip)
  `(tactic| (
    advance_reloc_begin (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect $pc 3 14 14) from
      xor_r32_r32_rex_effect_step $pc 0x45 0xf6 (by simp [RexNoWPrefix]) rfl)))
      next (boundary_ne_program $outside ($inside 3 (by decide)))
    advance_reloc_then (StepEffect.forgetFlags (h := (show StepEffect _ _ (xorR32R32Effect ($pc + 3) 2 0 0) from
      xor_r32_r32_effect_step ($pc + 3) 0xc0 rfl)))
      next (boundary_ne_program $outside ($inside 5 (by decide)))
    $extra:tactic
    advance_reloc_then (movzx_r32_r8_rex_effect_step ($pc + $(Lean.quote (if trait then 13 else 5)))
      0x44 (by simp [RexNoWPrefix]) $(Lean.quote (if fin then 0xe0 else 0xf8)) rfl)
      next (boundary_ne_program $outside ($inside $(Lean.quote (if trait then 17 else 9)) (by decide)))
    advance_finish [emptyEffect, emptyLength, tailReg, finalization, Finalization.variant,
      Finalize.Variant.registers, Blocks.Length.Registers.tail, BitVec.xor_self]))

theorem empty_run [Bindings] (p : BitVec 64) (form : Form) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (emptyLength form)) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (emptyBytes form))
      (Effect.post (emptyEffect p form)) := by
  cases form
  · reset_normalize_empty reset, p, outside, inside
  · reset_normalize_empty finalize, p, outside, inside
  · reset_normalize_empty trait, p, outside, inside

theorem empty_code (v : Wrapper.Variant) (form : Form) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (emptyEntry v form) (emptyBytes form)) s := by
  have h := programText_slice (programLoaded_codeIn loaded)
    (entryOffset true v form + (length true form - emptyLength form)) (emptyBytes form)
    (by cases form <;> cases v <;> decide +kernel)
    (by cases form <;> cases v <;> decide +kernel)
  simpa only [emptyEntry, entry, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem empty_inside (v : Wrapper.Variant) (form : Form) :
    BlockInProgram (emptyEntry v form) (emptyLength form) := by
  have h := blockInProgram_of_textOffset
    (entryOffset true v form + (length true form - emptyLength form)) (emptyLength form)
    (by cases form <;> cases v <;> decide +kernel)
  simpa only [emptyEntry, entry, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem empty_prepared {s t : RamState} {v : Wrapper.Variant} (form : Form)
    (hasher : HasherAt s (rspOf s + BitVec.ofNat 64 (bufferOffset true form)) ByteArray.empty v.initialHash)
    (result : (emptyEffect (emptyEntry v form) form s).Holds s t) :
    Finalize.Prepared ((finalization true form).layout v) (rspOf s) ByteArray.empty t := by
  have nextPC : emptyEntry v form + BitVec.ofNat 64 (emptyLength form) =
      ((finalization true form).layout v).entry := by
    cases form <;> cases v <;> decide +kernel
  have mem : t.external = s.external := by
    apply result.agrees.external
    cases form <;> simp [emptyEffect, Effect.components, Component.Covers]
  refine ⟨by cases form <;> exact result.rip.trans nextPC, ?_, ?_, ?_, ?_, ?_⟩
  · apply result.agrees.read (n := 64) (r := 4)
    cases form <;> simp [emptyEffect, Effect.components, tailReg, finalization,
      Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail]
  · exact hasher.of_bytes (fun i _ => congrArg (fun m => m[_]?) mem)
  · have w := result.writes
    cases form <;> simp_all [emptyEffect, tailReg, finalization, Finalization.layout,
      Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail,
      Write.AllHold, Operand.read]
  · have w := result.writes
    cases form <;> simp_all [emptyEffect, Finalize.countValue, tailReg, finalization,
      Finalization.layout, Finalization.variant, Finalize.Variant.registers,
      Blocks.Length.Registers.blocks, Blocks.Length.Registers.preShifted, Write.AllHold, Operand.read]
  · have w := result.writes
    cases form <;> simp_all [emptyEffect, finalization, Finalization.layout, Finalization.variant,
      Finalize.Variant.needsHashPointer, Finalize.Variant.hashReg, Finalize.Layout.hash,
      Finalize.Layout.buffer, Finalize.Variant.buffer, Blocks.Zero.Offset.value, Write.AllHold,
      Operand.read, BitVec.add_assoc]

end Sha2.Proofs.Reset.Normalize
