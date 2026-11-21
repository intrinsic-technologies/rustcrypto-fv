import P256.Proofs.Verifying.Combination.Entry

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def leftTableCopy1Bytes : List UInt8 :=
  [0x48, 0x8d, 0x9c, 0x24, 0x38, 0x1, 0x0, 0x0, 0xba, 0x0, 0x3, 0x0, 0x0, 0x48, 0x89, 0xdf, 0x48, 0x89, 0xee]

def leftTableCopy1Effect (s : RamState) : Effect :=
  { rip := 0x106597
    writes := [⟨(Operand.reg 3 : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 312⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem leftTableCopy1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106584)
      (codeRange 0x106584 leftTableCopy1Bytes) (Effect.post leftTableCopy1Effect) := by
  advance_begin (lea_r64_effect_step 0x106584 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x658c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10658c 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x106584 leftTableCopy1Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6591 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106591 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106584 leftTableCopy1Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6594 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106594 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106584 leftTableCopy1Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6597 (by decide))⟩
  advance_finish [leftTableCopy1Effect]

def leftTableCopy2Bytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0x68, 0xa, 0x0, 0x0, 0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x48, 0x89, 0xde]

def leftTableCopy2Effect (s : RamState) : Effect :=
  { rip := 0x1065ad
    writes := [⟨(Operand.reg 12 : Operand 64), (Operand.reg 4 : Operand 64).read s + 2664⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 2664⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem leftTableCopy2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10659a)
      (codeRange 0x10659a leftTableCopy2Bytes) (Effect.post leftTableCopy2Effect) := by
  advance_begin (lea_r64_effect_step 0x10659a 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 2664)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65a2 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1065a2 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x10659a leftTableCopy2Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65a7 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065a7 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10659a leftTableCopy2Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65aa (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065aa 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10659a leftTableCopy2Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65ad (by decide))⟩
  advance_finish [leftTableCopy2Effect]

def leftTableCopy3Bytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0x68, 0xd, 0x0, 0x0, 0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6]

def leftTableCopy3Effect (s : RamState) : Effect :=
  { rip := 0x1065c3
    writes := [⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 3432⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 3432⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem leftTableCopy3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1065b0)
      (codeRange 0x1065b0 leftTableCopy3Bytes) (Effect.post leftTableCopy3Effect) := by
  advance_begin (lea_r64_effect_step 0x1065b0 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 3432)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65b8 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1065b8 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x1065b0 leftTableCopy3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65bd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065bd 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065b0 leftTableCopy3Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65c0 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065c0 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065b0 leftTableCopy3Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65c3 (by decide))⟩
  advance_finish [leftTableCopy3Effect]

def leftTableCopy4Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x68, 0x13, 0x0, 0x0, 0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xee]

def leftTableCopy4Effect (s : RamState) : Effect :=
  { rip := 0x1065d6
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 4968⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem leftTableCopy4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1065c6)
      (codeRange 0x1065c6 leftTableCopy4Bytes) (Effect.post leftTableCopy4Effect) := by
  advance_begin (lea_r64_effect_step 0x1065c6 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 4968)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65ce (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1065ce 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x1065c6 leftTableCopy4Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65d3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065d3 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065c6 leftTableCopy4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65d6 (by decide))⟩
  advance_finish [leftTableCopy4Effect]

def rightTableBytes : List UInt8 :=
  [0xba, 0x1, 0x0, 0x0, 0x0, 0x48, 0x89, 0xef, 0x4c, 0x89, 0xfe]

def rightTableEffect (s : RamState) : Effect :=
  { rip := 0x1065e4
    writes := [⟨(Operand.reg 2 : Operand 64), 1⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem rightTable_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1065d9)
      (codeRange 0x1065d9 rightTableBytes) (Effect.post rightTableEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1065d9 0xba (by decide) 1)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65de (by decide))
  advance_then (mov_r64_r64_effect_step 0x1065de 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065d9 rightTableBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65e1 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065e1 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065d9 rightTableBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65e4 (by decide))⟩
  advance_finish [rightTableEffect]

def rightTableCopy1Bytes : List UInt8 :=
  [0xba, 0x0, 0x3, 0x0, 0x0, 0x48, 0x89, 0xdf, 0x48, 0x89, 0xee]

def rightTableCopy1Effect (s : RamState) : Effect :=
  { rip := 0x1065f4
    writes := [⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem rightTableCopy1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1065e9)
      (codeRange 0x1065e9 rightTableCopy1Bytes) (Effect.post rightTableCopy1Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1065e9 0xba (by decide) 768)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65ee (by decide))
  advance_then (mov_r64_r64_effect_step 0x1065ee 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065e9 rightTableCopy1Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65f1 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065f1 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065e9 rightTableCopy1Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65f4 (by decide))⟩
  advance_finish [rightTableCopy1Effect]

def rightTableCopy2Bytes : List UInt8 :=
  [0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x48, 0x89, 0xde]

def rightTableCopy2Effect (s : RamState) : Effect :=
  { rip := 0x106602
    writes := [⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem rightTableCopy2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1065f7)
      (codeRange 0x1065f7 rightTableCopy2Bytes) (Effect.post rightTableCopy2Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1065f7 0xba (by decide) 768)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x65fc (by decide))
  advance_then (mov_r64_r64_effect_step 0x1065fc 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065f7 rightTableCopy2Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x65ff (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1065ff 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1065f7 rightTableCopy2Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6602 (by decide))⟩
  advance_finish [rightTableCopy2Effect]

def rightTableCopy3Bytes : List UInt8 :=
  [0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6]

def rightTableCopy3Effect (s : RamState) : Effect :=
  { rip := 0x106610
    writes := [⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem rightTableCopy3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106605)
      (codeRange 0x106605 rightTableCopy3Bytes) (Effect.post rightTableCopy3Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x106605 0xba (by decide) 768)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x660a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10660a 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106605 rightTableCopy3Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x660d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10660d 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106605 rightTableCopy3Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6610 (by decide))⟩
  advance_finish [rightTableCopy3Effect]

def rightTableCopy4Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x68, 0x16, 0x0, 0x0, 0xba, 0x0, 0x3, 0x0, 0x0, 0x4c, 0x89, 0xee]

def rightTableCopy4Effect (s : RamState) : Effect :=
  { rip := 0x106623
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 5736⟩,
      ⟨(Operand.reg 2 : Operand 64), 768⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem rightTableCopy4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106613)
      (codeRange 0x106613 rightTableCopy4Bytes) (Effect.post rightTableCopy4Effect) := by
  advance_begin (lea_r64_effect_step 0x106613 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 5736)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x661b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10661b 0xba (by decide) 768)
  case sub => exact codeRange_slice_subset 0x106613 rightTableCopy4Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6620 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106620 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106613 rightTableCopy4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6623 (by decide))⟩
  advance_finish [rightTableCopy4Effect]

def tablePackBytes : List UInt8 :=
  [0xba, 0x0, 0x6, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x48, 0x8d, 0xb4, 0x24, 0x68, 0x13, 0x0, 0x0]

def tablePackEffect (s : RamState) : Effect :=
  { rip := 0x106636
    writes := [⟨(Operand.reg 2 : Operand 64), 1536⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 4968⟩] }

theorem tablePack_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106626)
      (codeRange 0x106626 tablePackBytes) (Effect.post tablePackEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x106626 0xba (by decide) 1536)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x662b (by decide))
  advance_then (mov_r64_r64_effect_step 0x10662b 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106626 tablePackBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x662e (by decide))⟩
  advance_then (lea_r64_effect_step 0x10662e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 4968)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106626 tablePackBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6636 (by decide))⟩
  advance_finish [tablePackEffect]

end P256.Proofs.Verifying.Combination.Preparation
