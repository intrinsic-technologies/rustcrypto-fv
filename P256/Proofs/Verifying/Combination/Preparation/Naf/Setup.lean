import P256.Proofs.Verifying.Combination.Entry

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def firstCopy1Bytes : List UInt8 :=
  [0x4c, 0x8d, 0xa4, 0x24, 0x68, 0xa, 0x0, 0x0, 0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x48, 0x89, 0xde]

def firstCopy1Effect (s : RamState) : Effect :=
  { rip := 0x10669c
    writes := [⟨(Operand.reg 12 : Operand 64), (Operand.reg 4 : Operand 64).read s + 2664⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 2664⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem firstCopy1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106689)
      (codeRange 0x106689 firstCopy1Bytes) (Effect.post firstCopy1Effect) := by
  advance_begin (lea_r64_effect_step 0x106689 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 2664)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6691 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x106691 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x106689 firstCopy1Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6696 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106696 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106689 firstCopy1Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6699 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106699 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106689 firstCopy1Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x669c (by decide))⟩
  advance_finish [firstCopy1Effect]

def firstCopy2Bytes : List UInt8 :=
  [0x4c, 0x8d, 0xac, 0x24, 0x38, 0x4, 0x0, 0x0, 0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6]

def firstCopy2Effect (s : RamState) : Effect :=
  { rip := 0x1066b2
    writes := [⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1080⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1080⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem firstCopy2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10669f)
      (codeRange 0x10669f firstCopy2Bytes) (Effect.post firstCopy2Effect) := by
  advance_begin (lea_r64_effect_step 0x10669f 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1080)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x66a7 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1066a7 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x10669f firstCopy2Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66ac (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066ac 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10669f firstCopy2Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66af (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066af 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10669f firstCopy2Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66b2 (by decide))⟩
  advance_finish [firstCopy2Effect]

def firstCopy3Bytes : List UInt8 :=
  [0x4c, 0x8d, 0xbc, 0x24, 0x68, 0x7, 0x0, 0x0, 0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xee]

def firstCopy3Effect (s : RamState) : Effect :=
  { rip := 0x1066c8
    writes := [⟨(Operand.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1896⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1896⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem firstCopy3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1066b5)
      (codeRange 0x1066b5 firstCopy3Bytes) (Effect.post firstCopy3Effect) := by
  advance_begin (lea_r64_effect_step 0x1066b5 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1896)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x66bd (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1066bd 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x1066b5 firstCopy3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66c2 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066c2 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066b5 firstCopy3Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66c5 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066c5 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066b5 firstCopy3Bytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66c8 (by decide))⟩
  advance_finish [firstCopy3Effect]

def firstCopy4Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x48, 0x5, 0x0, 0x0, 0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xfe]

def firstCopy4Effect (s : RamState) : Effect :=
  { rip := 0x1066db
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1352⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem firstCopy4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1066cb)
      (codeRange 0x1066cb firstCopy4Bytes) (Effect.post firstCopy4Effect) := by
  advance_begin (lea_r64_effect_step 0x1066cb 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x66d3 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1066d3 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x1066cb firstCopy4Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66d8 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066d8 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066cb firstCopy4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66db (by decide))⟩
  advance_finish [firstCopy4Effect]

def secondScalarBytes : List UInt8 :=
  [0xba, 0x1, 0x0, 0x0, 0x0, 0x48, 0x89, 0xdf, 0x48, 0x89, 0xee]

def secondScalarEffect (s : RamState) : Effect :=
  { rip := 0x1066e9
    writes := [⟨(Operand.reg 2 : Operand 64), 1⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem secondScalar_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1066de)
      (codeRange 0x1066de secondScalarBytes) (Effect.post secondScalarEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1066de 0xba (by decide) 1)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x66e3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1066e3 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066de secondScalarBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66e6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066e6 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066de secondScalarBytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66e9 (by decide))⟩
  advance_finish [secondScalarEffect]

def secondCopy1Bytes : List UInt8 :=
  [0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xe7, 0x48, 0x89, 0xde]

def secondCopy1Effect (s : RamState) : Effect :=
  { rip := 0x1066f9
    writes := [⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

theorem secondCopy1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1066ee)
      (codeRange 0x1066ee secondCopy1Bytes) (Effect.post secondCopy1Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1066ee 0xba (by decide) 272)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x66f3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1066f3 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066ee secondCopy1Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66f6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1066f6 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066ee secondCopy1Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x66f9 (by decide))⟩
  advance_finish [secondCopy1Effect]

def secondCopy2Bytes : List UInt8 :=
  [0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xe6]

def secondCopy2Effect (s : RamState) : Effect :=
  { rip := 0x106707
    writes := [⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩] }

theorem secondCopy2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1066fc)
      (codeRange 0x1066fc secondCopy2Bytes) (Effect.post secondCopy2Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1066fc 0xba (by decide) 272)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6701 (by decide))
  advance_then (mov_r64_r64_effect_step 0x106701 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066fc secondCopy2Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6704 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106704 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1066fc secondCopy2Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6707 (by decide))⟩
  advance_finish [secondCopy2Effect]

def secondCopy3Bytes : List UInt8 :=
  [0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xee]

def secondCopy3Effect (s : RamState) : Effect :=
  { rip := 0x106715
    writes := [⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩] }

theorem secondCopy3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10670a)
      (codeRange 0x10670a secondCopy3Bytes) (Effect.post secondCopy3Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10670a 0xba (by decide) 272)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x670f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10670f 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10670a secondCopy3Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6712 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106712 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10670a secondCopy3Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6715 (by decide))⟩
  advance_finish [secondCopy3Effect]

def secondCopy4Bytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x58, 0x6, 0x0, 0x0, 0xba, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x89, 0xfe]

def secondCopy4Effect (s : RamState) : Effect :=
  { rip := 0x106728
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1624⟩,
      ⟨(Operand.reg 2 : Operand 64), 272⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩] }

theorem secondCopy4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106718)
      (codeRange 0x106718 secondCopy4Bytes) (Effect.post secondCopy4Effect) := by
  advance_begin (lea_r64_effect_step 0x106718 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1624)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6720 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x106720 0xba (by decide) 272)
  case sub => exact codeRange_slice_subset 0x106718 secondCopy4Bytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6725 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106725 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106718 secondCopy4Bytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6728 (by decide))⟩
  advance_finish [secondCopy4Effect]

def scalarPackBytes : List UInt8 :=
  [0xba, 0x20, 0x2, 0x0, 0x0, 0x4c, 0x89, 0xff, 0x48, 0x8d, 0xb4, 0x24, 0x48, 0x5, 0x0, 0x0]

def scalarPackEffect (s : RamState) : Effect :=
  { rip := 0x10673b
    writes := [⟨(Operand.reg 2 : Operand 64), 544⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 1352⟩] }

theorem scalarPack_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10672b)
      (codeRange 0x10672b scalarPackBytes) (Effect.post scalarPackEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10672b 0xba (by decide) 544)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6730 (by decide))
  advance_then (mov_r64_r64_effect_step 0x106730 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10672b scalarPackBytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6733 (by decide))⟩
  advance_then (lea_r64_effect_step 0x106733 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10672b scalarPackBytes 8 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x673b (by decide))⟩
  advance_finish [scalarPackEffect]

end P256.Proofs.Verifying.Combination.Preparation.Naf
