import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareCopy0Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x48,0x89,0xef,0x49,0x89,0xee,0x4c,0x89,0xe6]

def prepareCopy0Effect (s : RamState) : Effect :=
  { rip := 0x10454d
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 14 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10453f)
      (codeRange 0x10453f prepareCopy0Bytes) (Effect.post prepareCopy0Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10453f 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4544 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104544 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10453f prepareCopy0Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4547 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104547 0x49 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10453f prepareCopy0Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x454a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10454a 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10453f prepareCopy0Bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x454d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy1Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy1Effect (s : RamState) : Effect :=
  { rip := 0x1045b7
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy1_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1045ac)
      (codeRange 0x1045ac prepareCopy1Bytes) (Effect.post prepareCopy1Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1045ac 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x45b1 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1045b1 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1045ac prepareCopy1Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45b4 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1045b4 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1045ac prepareCopy1Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x45b7 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy1Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy2Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy2Effect (s : RamState) : Effect :=
  { rip := 0x10461f
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy2_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104614)
      (codeRange 0x104614 prepareCopy2Bytes) (Effect.post prepareCopy2Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x104614 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4619 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104619 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104614 prepareCopy2Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x461c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10461c 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x104614 prepareCopy2Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x461f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy2Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy3Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy3Effect (s : RamState) : Effect :=
  { rip := 0x104687
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy3_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10467c)
      (codeRange 0x10467c prepareCopy3Bytes) (Effect.post prepareCopy3Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10467c 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4681 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104681 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10467c prepareCopy3Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4684 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104684 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10467c prepareCopy3Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4687 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy3Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy4Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy4Effect (s : RamState) : Effect :=
  { rip := 0x1046ef
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy4_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1046e4)
      (codeRange 0x1046e4 prepareCopy4Bytes) (Effect.post prepareCopy4Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1046e4 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x46e9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1046e9 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1046e4 prepareCopy4Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46ec (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1046ec 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1046e4 prepareCopy4Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x46ef (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy4Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy5Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy5Effect (s : RamState) : Effect :=
  { rip := 0x104757
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy5_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10474c)
      (codeRange 0x10474c prepareCopy5Bytes) (Effect.post prepareCopy5Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10474c 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4751 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104751 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10474c prepareCopy5Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4754 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104754 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10474c prepareCopy5Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4757 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy5Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy6Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy6Effect (s : RamState) : Effect :=
  { rip := 0x1047bf
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy6_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1047b4)
      (codeRange 0x1047b4 prepareCopy6Bytes) (Effect.post prepareCopy6Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1047b4 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x47b9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1047b9 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1047b4 prepareCopy6Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47bc (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1047bc 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1047b4 prepareCopy6Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x47bf (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy6Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

def prepareCopy7Bytes : List UInt8 := [0xb9,0xc,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6]

def prepareCopy7Effect (s : RamState) : Effect :=
  { rip := 0x10482a
    writes := [⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r14⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r12⟩] }

set_option maxHeartbeats 800000 in
theorem prepareCopy7_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10481f)
      (codeRange 0x10481f prepareCopy7Bytes) (Effect.post prepareCopy7Effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10481f 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4824 (by decide))
  advance_then (mov_r64_r64_effect_step 0x104824 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10481f prepareCopy7Bytes 5 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4827 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x104827 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10481f prepareCopy7Bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x482a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareCopy7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareCopy7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareCopy7Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Scanning
