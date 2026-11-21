import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Buffered.Update.Contracts

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def slicesLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x4e, 0x8b, 0x34, 0xf8,
    0x48, 0x8b, 0x84, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x4a, 0x8b, 0x1c, 0xf8]

def stackWord (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.mem (stackPtr s + offset) : Operand 64).read s

def sliceTableAddress (s : RamState) (offset : BitVec 64) (index : BitVec 5) : BitVec 64 :=
  stackWord s offset + ((Operand.reg index : Operand 64).read s <<< 3)

structure SliceLoadPre (entry pointerOffset lengthOffset : BitVec 64) (index : BitVec 5)
    (s : RamState) : Prop where
  rip : s.RIP = entry
  pointerSlot : MemReadable s (stackPtr s + pointerOffset) 8
  lengthSlot : MemReadable s (stackPtr s + lengthOffset) 8
  pointerEntry : MemReadable s (sliceTableAddress s pointerOffset index) 8
  lengthEntry : MemReadable s (sliceTableAddress s lengthOffset index) 8

def sliceLoadEffect (exit pointerSlot lengthSlot : BitVec 64)
    (index pointerRegister lengthRegister : BitVec 5) (s : RamState) : Effect where
  rip := exit
  writes :=
    [⟨(.reg pointerRegister : Operand 64),
       (Operand.mem (sliceTableAddress s pointerSlot index) : Operand 64).read s⟩,
     ⟨(.reg 0 : Operand 64), stackWord s lengthSlot⟩,
     ⟨(.reg lengthRegister : Operand 64),
       (Operand.mem (sliceTableAddress s lengthSlot index) : Operand 64).read s⟩]

macro "md5_load_tables " p0:term "," p1:term "," p2:term "," p3:term "," p4:term
    ";" ptr:term "," len:term ";" index:term "," rexP:term "," regP:term ","
    rexL:term "," regL:term : tactic => do
  let off1 := Lean.quote (p1.raw.isNatLit?.getD 0 - 0x100000)
  let off2 := Lean.quote (p2.raw.isNatLit?.getD 0 - 0x100000)
  let off3 := Lean.quote (p3.raw.isNatLit?.getD 0 - 0x100000)
  let off4 := Lean.quote (p4.raw.isNatLit?.getD 0 - 0x100000)
  `(tactic| (
  md5_run_begin (mov_r64_m64_effect_step $p0 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d32 $ptr)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, h.pointerSlot⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off1 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p1 $rexP (by unfold RexWPrefix; decide) $regP
    (.sib 0 (some $index) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa [sliceTableAddress, stackWord, stackPtr] using h.pointerEntry
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off2 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p2 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d32 $len)) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact h.lengthSlot
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off3 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p3 $rexL (by unfold RexWPrefix; decide) $regL
    (.sib 0 (some $index) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa [sliceTableAddress, stackWord, stackPtr] using h.lengthEntry
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off4 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [sliceLoadEffect]
  · x86_norm [sliceLoadEffect, sliceTableAddress, stackWord, BitVec.add_zero]
  · intro i; cases i <;> x86_norm [sliceLoadEffect]
  · x86_norm [sliceLoadEffect]
  case sub => apply codeRange_mem_of_drop (p := $p0) 20; decide +kernel
  case sub => apply codeRange_mem_of_drop (p := $p0) 12; decide +kernel
  case sub => apply codeRange_mem_of_drop (p := $p0) 8; decide +kernel))

theorem slices_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x10033d 0xb0 0xb8 15)
      (codeRange 0x10033d slicesLoadBytes) (sliceLoadEffect 0x100355 0xb0 0xb8 15 14 3) := by
  unfold slicesLoadBytes
  md5_load_tables 0x10033d, 0x100345, 0x100349, 0x100351, 0x100355;
    0xb0, 0xb8; 15, 0x4e, 6, 0x4a, 3

def resetFirstLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x4e, 0x8b, 0x24, 0xf8,
    0x48, 0x8b, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x4e, 0x8b, 0x34, 0xf8]

theorem resetFirst_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x1006b8 0xc8 0xd0 15)
      (codeRange 0x1006b8 resetFirstLoadBytes) (sliceLoadEffect 0x1006d0 0xc8 0xd0 15 12 14) := by
  unfold resetFirstLoadBytes
  md5_load_tables 0x1006b8, 0x1006c0, 0x1006c4, 0x1006cc, 0x1006d0;
    0xc8, 0xd0; 15, 0x4e, 4, 0x4e, 6

def resetSecondLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x34, 0xe8,
    0x48, 0x8b, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x4c, 0x8b, 0x24, 0xe8]

theorem resetSecond_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x1009c7 0xc8 0xd0 5)
      (codeRange 0x1009c7 resetSecondLoadBytes) (sliceLoadEffect 0x1009df 0xc8 0xd0 5 6 12) := by
  unfold resetSecondLoadBytes
  md5_load_tables 0x1009c7, 0x1009cf, 0x1009d3, 0x1009db, 0x1009df;
    0xc8, 0xd0; 5, 0x48, 6, 0x4c, 4

theorem updateFinalizeInto_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x1018ed 0xb0 0xb8 15)
      (codeRange 0x1018ed slicesLoadBytes) (sliceLoadEffect 0x101905 0xb0 0xb8 15 14 3) := by
  unfold slicesLoadBytes
  md5_load_tables 0x1018ed, 0x1018f5, 0x1018f9, 0x101901, 0x101905;
    0xb0, 0xb8; 15, 0x4e, 6, 0x4a, 3

macro "md5_reset_load_tables " p0:term "," p1:term "," p2:term "," p3:term "," p4:term
    ";" ptr:term "," len:term ";" index:term "," rexP:term "," regP:term ","
    rexL:term "," regL:term : tactic => do
  let off1 := Lean.quote (p1.raw.isNatLit?.getD 0 - 0x100000)
  let off2 := Lean.quote (p2.raw.isNatLit?.getD 0 - 0x100000)
  let off3 := Lean.quote (p3.raw.isNatLit?.getD 0 - 0x100000)
  let off4 := Lean.quote (p4.raw.isNatLit?.getD 0 - 0x100000)
  `(tactic| (
  md5_run_begin (mov_r64_m64_effect_step $p0 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d8 $ptr)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, h.pointerSlot⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off1 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p1 $rexP (by unfold RexWPrefix; decide) $regP
    (.sib 0 (some $index) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa [sliceTableAddress, stackWord, stackPtr] using h.pointerEntry
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off2 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p2 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d8 $len)) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact h.lengthSlot
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off3 (by decide +kernel)
  md5_run_then (mov_r64_m64_effect_step $p3 $rexL (by unfold RexWPrefix; decide) $regL
    (.sib 0 (some $index) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa [sliceTableAddress, stackWord, stackPtr] using h.lengthEntry
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption)
      $off4 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [sliceLoadEffect]
  · x86_norm [sliceLoadEffect, sliceTableAddress, stackWord, BitVec.add_zero]
  · intro i; cases i <;> x86_norm [sliceLoadEffect]
  · x86_norm [sliceLoadEffect]
  case sub => apply codeRange_mem_of_drop (p := $p0) 14; decide +kernel
  case sub => apply codeRange_mem_of_drop (p := $p0) 9; decide +kernel
  case sub => apply codeRange_mem_of_drop (p := $p0) 5; decide +kernel))

def resetDiscardFirstLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x10, 0x4a, 0x8b, 0x1c, 0xf8, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x4e, 0x8b, 0x34, 0xf8]

theorem resetDiscardFirst_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x1013f8 16 24 15)
      (codeRange 0x1013f8 resetDiscardFirstLoadBytes)
      (sliceLoadEffect 0x10140a 16 24 15 3 14) := by
  unfold resetDiscardFirstLoadBytes
  md5_reset_load_tables 0x1013f8, 0x1013fd, 0x101401, 0x101406, 0x10140a;
    16, 24; 15, 0x4a, 3, 0x4e, 6

def resetDiscardSecondLoadBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x10, 0x4a, 0x8b, 0x1c, 0xe0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x4e, 0x8b, 0x2c, 0xe0]

theorem resetDiscardSecond_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x101537 16 24 12)
      (codeRange 0x101537 resetDiscardSecondLoadBytes)
      (sliceLoadEffect 0x101549 16 24 12 3 13) := by
  unfold resetDiscardSecondLoadBytes
  md5_reset_load_tables 0x101537, 0x10153c, 0x101540, 0x101545, 0x101549;
    16, 24; 12, 0x4a, 3, 0x4e, 5

theorem finalizeResetFirst_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x100d68 0xc8 0xd0 15)
      (codeRange 0x100d68 resetFirstLoadBytes)
      (sliceLoadEffect 0x100d80 0xc8 0xd0 15 12 14) := by
  unfold resetFirstLoadBytes
  md5_load_tables 0x100d68, 0x100d70, 0x100d74, 0x100d7c, 0x100d80;
    0xc8, 0xd0; 15, 0x4e, 4, 0x4e, 6

theorem finalizeResetSecond_load [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (SliceLoadPre 0x101057 0xc8 0xd0 5)
      (codeRange 0x101057 resetSecondLoadBytes)
      (sliceLoadEffect 0x10106f 0xc8 0xd0 5 6 12) := by
  unfold resetSecondLoadBytes
  md5_load_tables 0x101057, 0x10105f, 0x101063, 0x10106b, 0x10106f;
    0xc8, 0xd0; 5, 0x48, 6, 0x4c, 4

namespace LoopKind

abbrev Kind := Buffered.UpdateKind

def entry : Kind → BitVec 64
  | .slices => 0x10033d
  | .resetFirst => 0x1006b8
  | .resetSecond => 0x1009c7
  | .updateFinalizeInto => 0x1018ed
  | .finalizeResetFirst => 0x100d68
  | .finalizeResetSecond => 0x101057
  | .resetDiscardFirst => 0x1013f8
  | .resetDiscardSecond => 0x101537

def indexRegister : Kind → BitVec 5
  | .slices | .resetFirst | .updateFinalizeInto | .finalizeResetFirst | .resetDiscardFirst => 15
  | .resetSecond | .finalizeResetSecond => 5
  | .resetDiscardSecond => 12

def pointerOffset : Kind → BitVec 64
  | .slices | .updateFinalizeInto => 0xb0
  | .resetFirst | .resetSecond | .finalizeResetFirst | .finalizeResetSecond => 0xc8
  | .resetDiscardFirst | .resetDiscardSecond => 16

def lengthOffset : Kind → BitVec 64
  | .slices | .updateFinalizeInto => 0xb8
  | .resetFirst | .resetSecond | .finalizeResetFirst | .finalizeResetSecond => 0xd0
  | .resetDiscardFirst | .resetDiscardSecond => 24

def loadBytes : Kind → List UInt8
  | .slices | .updateFinalizeInto => slicesLoadBytes
  | .resetFirst | .finalizeResetFirst => resetFirstLoadBytes
  | .resetSecond | .finalizeResetSecond => resetSecondLoadBytes
  | .resetDiscardFirst => resetDiscardFirstLoadBytes
  | .resetDiscardSecond => resetDiscardSecondLoadBytes

def loadPre (kind : Kind) : RamState → Prop :=
  SliceLoadPre (entry kind) (pointerOffset kind) (lengthOffset kind) (indexRegister kind)

def loadEffect (kind : Kind) : RamState → Effect :=
  sliceLoadEffect (Buffered.UpdateKind.entry kind) (pointerOffset kind) (lengthOffset kind)
    (indexRegister kind) kind.inputRegister kind.sizeRegister

end LoopKind

theorem load_slice [Bindings] (kind : LoopKind.Kind) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : LoopKind.loadPre kind s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (LoopKind.loadEffect kind s).Holds s t := by
  have hBlock : AdvancesBlock boundary (LoopKind.loadPre kind)
      (codeRange (LoopKind.entry kind) (LoopKind.loadBytes kind)) (LoopKind.loadEffect kind) := by
    cases kind
    · exact slices_load boundary hOutside
    · exact resetFirst_load boundary hOutside
    · exact resetSecond_load boundary hOutside
    · exact updateFinalizeInto_load boundary hOutside
    · exact finalizeResetFirst_load boundary hOutside
    · exact finalizeResetSecond_load boundary hOutside
    · exact resetDiscardFirst_load boundary hOutside
    · exact resetDiscardSecond_load boundary hOutside
  have hBytes : CodeIn (codeRange (LoopKind.entry kind) (LoopKind.loadBytes kind)) s := by
    cases kind
    · exact program_text_slice hCode 0x33d 24 (by decide +kernel)
    · exact program_text_slice hCode 0x6b8 24 (by decide +kernel)
    · exact program_text_slice hCode 0x9c7 24 (by decide +kernel)
    · exact program_text_slice hCode 0x18ed 24 (by decide +kernel)
    · exact program_text_slice hCode 0xd68 24 (by decide +kernel)
    · exact program_text_slice hCode 0x1057 24 (by decide +kernel)
    · exact program_text_slice hCode 0x13f8 18 (by decide +kernel)
    · exact program_text_slice hCode 0x1537 18 (by decide +kernel)
  obtain ⟨fuel, t, hAdvance, hReady', _, hEffect⟩ := hBlock s hReady hBytes hPre
  refine ⟨fuel, t, hAdvance, hReady', hEffect.codeIn ?_ hCode, hEffect⟩
  apply Effect.Avoids.of_noMem
  cases kind <;> simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
    Write.component, Operand.component, Component.Covers]

end Md5.Proofs.Streaming
