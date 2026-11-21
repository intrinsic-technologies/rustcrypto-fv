import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Field.Schoolbook.Frame

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulFlags64 mulHigh64 mul_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec.Program.Routines

open P256.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

def upperProductsBytes : List UInt8 :=
  [
    0x48, 0x89, 0xd8, 0x48, 0xf7, 0xe1, 0x49, 0x89, 0xd7, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4c, 0x89,
    0xf0, 0x48, 0xf7, 0xe1, 0x49, 0x89, 0xd5, 0x48, 0x89, 0x44, 0x24, 0x30, 0x4c, 0x8b, 0x54, 0x24,
    0x48, 0x4c, 0x89, 0xd0, 0x48, 0xf7, 0xe1, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xd5, 0x4c,
    0x8b, 0x76, 0x10, 0x48, 0x8b, 0x74, 0x24, 0x40, 0x48, 0x89, 0xf0, 0x48, 0xf7, 0xe1, 0x49, 0x89,
    0xd1, 0x48, 0x89, 0x44, 0x24, 0x8, 0x4c, 0x89, 0xd0, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0xd3, 0x48,
    0x89, 0xc1, 0x48, 0x89, 0xf0, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0xd6, 0x49, 0x89, 0xc2]

structure UpperProductsPre (s : RamState) : Prop extends ScratchPre 0x11ca70 94 s where
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s + 16) 8
  apart : ∀ c ∈ ([16, 48, 32] : List (BitVec 64)),
    RangeApart (rspOf s + c) 8 ((Operand.reg 6 : Operand 64).read s + 16) 8

def upperProductsHighEffect (s : RamState) : Effect :=
  let a3 := (Operand.reg 1 : Operand 64).read s
  let b3 := (Operand.reg 3 : Operand 64).read s
  let b2 := (Operand.reg 14 : Operand 64).read s
  { rip := 0x11ca8c
    writes := [
      ⟨(Operand.reg 15 : Operand 64), mulHigh64 b3 a3⟩,
      ⟨(Operand.mem (rspOf s + 16) : Operand 64), b3 * a3⟩,
      ⟨(Operand.reg 0 : Operand 64), b2 * a3⟩,
      ⟨(Operand.reg 2 : Operand 64), mulHigh64 b2 a3⟩,
      ⟨(Operand.reg 13 : Operand 64), mulHigh64 b2 a3⟩,
      ⟨(Operand.mem (rspOf s + 48) : Operand 64), b2 * a3⟩]
    flags := some (mulFlags64 b2 a3) }

def upperProductsCrossEffect (s : RamState) : Effect :=
  let a3 := (Operand.reg 1 : Operand 64).read s
  let a2 := (Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s
  let b3 := (Operand.reg 3 : Operand 64).read s
  let b2 := (Operand.reg 14 : Operand 64).read s
  let b1 := (Operand.mem (rspOf s + 72) : Operand 64).read s
  let b0 := (Operand.mem (rspOf s + 64) : Operand 64).read s
  { rip := 0x11cab6
    writes := [
      ⟨(Operand.reg 15 : Operand 64), mulHigh64 b3 a3⟩,
      ⟨(Operand.mem (rspOf s + 16) : Operand 64), b3 * a3⟩,
      ⟨(Operand.reg 13 : Operand 64), mulHigh64 b2 a3⟩,
      ⟨(Operand.mem (rspOf s + 48) : Operand 64), b2 * a3⟩,
      ⟨(Operand.reg 10 : Operand 64), b1⟩,
      ⟨(Operand.mem (rspOf s + 32) : Operand 64), b1 * a3⟩,
      ⟨(Operand.reg 5 : Operand 64), mulHigh64 b1 a3⟩,
      ⟨(Operand.reg 14 : Operand 64), a2⟩,
      ⟨(Operand.reg 6 : Operand 64), b0⟩,
      ⟨(Operand.reg 0 : Operand 64), b0 * a3⟩,
      ⟨(Operand.reg 2 : Operand 64), mulHigh64 b0 a3⟩,
      ⟨(Operand.reg 9 : Operand 64), mulHigh64 b0 a3⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), b0 * a3⟩]
    flags := some (mulFlags64 b0 a3) }

def upperProductsEffect (s : RamState) : Effect :=
  let a3 := (Operand.reg 1 : Operand 64).read s
  let a2 := (Operand.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s
  let b3 := (Operand.reg 3 : Operand 64).read s
  let b2 := (Operand.reg 14 : Operand 64).read s
  let b1 := (Operand.mem (rspOf s + 72) : Operand 64).read s
  let b0 := (Operand.mem (rspOf s + 64) : Operand 64).read s
  { rip := 0x11cace
    writes := [
      ⟨(Operand.reg 15 : Operand 64), mulHigh64 b3 a3⟩,
      ⟨(Operand.mem (rspOf s + 16) : Operand 64), b3 * a3⟩,
      ⟨(Operand.reg 13 : Operand 64), mulHigh64 b2 a3⟩,
      ⟨(Operand.mem (rspOf s + 48) : Operand 64), b2 * a3⟩,
      ⟨(Operand.mem (rspOf s + 32) : Operand 64), b1 * a3⟩,
      ⟨(Operand.reg 5 : Operand 64), mulHigh64 b1 a3⟩,
      ⟨(Operand.reg 14 : Operand 64), a2⟩,
      ⟨(Operand.reg 9 : Operand 64), mulHigh64 b0 a3⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), b0 * a3⟩,
      ⟨(Operand.reg 3 : Operand 64), mulHigh64 b1 a2⟩,
      ⟨(Operand.reg 1 : Operand 64), b1 * a2⟩,
      ⟨(Operand.reg 0 : Operand 64), b0 * a2⟩,
      ⟨(Operand.reg 2 : Operand 64), mulHigh64 b0 a2⟩,
      ⟨(Operand.reg 6 : Operand 64), mulHigh64 b0 a2⟩,
      ⟨(Operand.reg 10 : Operand 64), b0 * a2⟩]
    flags := some (mulFlags64 b0 a2) }

theorem upperProductsBytes_extracted :
    Extracted.textBytes.toListFrom 0x1ca70 94 = upperProductsBytes := by
  decide +kernel

macro "upper_products_then " step:term:max off:num len:num : tactic => `(tactic| (
  advance_then $step
  case sub => exact codeRange_slice_subset 0x11ca70 upperProductsBytes $off $len
  case mid =>
    intro s t hP hH hO
    have hframe := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · first
      | exact hH.rip_of (by x86_norm)
      | (refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
         x86_norm
         first | schoolbook_frame | exact hP.left)
      | (refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
         · x86_norm
           schoolbook_frame
         · x86_norm
           exact hframe.apart _ (by decide +kernel) $off $len (by decide +kernel))
    · schoolbook_avoid
    · x86_norm
      apply boundary_ne_program (by assumption)
      exact inProgram_of_textOffset (0x1ca70 + $off + $len) (by decide)))

set_option maxHeartbeats 800000 in
theorem upper_products_high [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary UpperProductsPre (codeRange 0x11ca70 upperProductsBytes)
      (Effect.post upperProductsHighEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x11ca70 0x48 0xd8 (by simp [RexWPrefix]) (by decide +kernel))
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ca73 (by decide))
  upper_products_then (mul_r64_effect_step 0x11ca73 0x48 0xe1
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 3 3
  upper_products_then (mov_r64_r64_effect_step 0x11ca76 0x49 0xd7
    (by simp [RexWPrefix]) (by decide +kernel)) 6 3
  upper_products_then (mov_m64_r64_effect_step 0x11ca79 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl) 9 5
  upper_products_then (mov_r64_r64_effect_step 0x11ca7e 0x4c 0xf0
    (by simp [RexWPrefix]) (by decide +kernel)) 14 3
  upper_products_then (mul_r64_effect_step 0x11ca81 0x48 0xe1
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 17 3
  upper_products_then (mov_r64_r64_effect_step 0x11ca84 0x49 0xd5
    (by simp [RexWPrefix]) (by decide +kernel)) 20 3
  upper_products_then (mov_m64_r64_effect_step 0x11ca87 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl) 23 5
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperProductsHighEffect]
  · x86_norm [upperProductsHighEffect]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [upperProductsHighEffect] <;> (repeat constructor <;> rfl)
  · x86_norm [upperProductsHighEffect]

set_option maxHeartbeats 800000 in
theorem upper_products_cross [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary UpperProductsPre (codeRange 0x11ca70 upperProductsBytes)
      (Effect.post upperProductsHighEffect) →
    AdvanceTriple boundary UpperProductsPre (codeRange 0x11ca70 upperProductsBytes)
      (Effect.post upperProductsCrossEffect) := by
  unfold upperProductsHighEffect
  upper_products_then (mov_r64_m64_effect_step 0x11ca8c 0x4c
    (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl) 28 5
  upper_products_then (mov_r64_r64_effect_step 0x11ca91 0x4c 0xd0
    (by simp [RexWPrefix]) (by decide +kernel)) 33 3
  upper_products_then (mul_r64_effect_step 0x11ca94 0x48 0xe1
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 36 3
  upper_products_then (mov_m64_r64_effect_step 0x11ca97 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl) 39 5
  upper_products_then (mov_r64_r64_effect_step 0x11ca9c 0x48 0xd5
    (by simp [RexWPrefix]) (by decide +kernel)) 44 3
  upper_products_then (mov_r64_m64_effect_step 0x11ca9f 0x4c
    (by simp [RexWPrefix]) 6 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl) 47 4
  upper_products_then (mov_r64_m64_effect_step 0x11caa3 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl) 51 5
  upper_products_then (mov_r64_r64_effect_step 0x11caa8 0x48 0xf0
    (by simp [RexWPrefix]) (by decide +kernel)) 56 3
  upper_products_then (mul_r64_effect_step 0x11caab 0x48 0xe1
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 59 3
  upper_products_then (mov_r64_r64_effect_step 0x11caae 0x49 0xd1
    (by simp [RexWPrefix]) (by decide +kernel)) 62 3
  upper_products_then (mov_m64_r64_effect_step 0x11cab1 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl) 65 5
  apply AdvanceTriple.block_end
  intro s t hP hH
  have ha16 (mem : Ram) (v : BitVec 64) :=
    memLoad_memStore_rangeApart mem _ _ v 64 (hP.apart 16 (by simp))
  have ha48 (mem : Ram) (v : BitVec 64) :=
    memLoad_memStore_rangeApart mem _ _ v 64 (hP.apart 48 (by simp))
  x86_norm at ha16 ha48
  apply hH.weaken
  · x86_norm [upperProductsCrossEffect]
  · x86_norm [upperProductsCrossEffect]
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
    rw [memLoad_memStore_rangeApart _ _ _ _ _ (hP.apart 32 (by simp))]
    x86_norm [ha16, ha48]
  · intro i; cases i <;> x86_norm [upperProductsCrossEffect] <;> (repeat constructor <;> rfl)
  · x86_norm [upperProductsCrossEffect]

set_option maxHeartbeats 800000 in
theorem upper_products_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary UpperProductsPre (codeRange 0x11ca70 upperProductsBytes)
      (Effect.post upperProductsEffect) := by
  have block := upper_products_cross boundary hout (upper_products_high boundary hout)
  revert block
  unfold upperProductsCrossEffect
  upper_products_then (mov_r64_r64_effect_step 0x11cab6 0x4c 0xd0
    (by simp [RexWPrefix]) (by decide +kernel)) 70 3
  upper_products_then (mul_r64_effect_step 0x11cab9 0x49 0xe6
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 73 3
  upper_products_then (mov_r64_r64_effect_step 0x11cabc 0x48 0xd3
    (by simp [RexWPrefix]) (by decide +kernel)) 76 3
  upper_products_then (mov_r64_r64_effect_step 0x11cabf 0x48 0xc1
    (by simp [RexWPrefix]) (by decide +kernel)) 79 3
  upper_products_then (mov_r64_r64_effect_step 0x11cac2 0x48 0xf0
    (by simp [RexWPrefix]) (by decide +kernel)) 82 3
  upper_products_then (mul_r64_effect_step 0x11cac5 0x49 0xe6
    (by simp [RexWPrefix]) (by decide +kernel) (by decide +kernel)) 85 3
  upper_products_then (mov_r64_r64_effect_step 0x11cac8 0x48 0xd6
    (by simp [RexWPrefix]) (by decide +kernel)) 88 3
  upper_products_then (mov_r64_r64_effect_step 0x11cacb 0x49 0xc2
    (by simp [RexWPrefix]) (by decide +kernel)) 91 3
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [upperProductsEffect]
  · x86_norm [upperProductsEffect] <;> (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [upperProductsEffect] <;> (repeat constructor <;> rfl)
  · x86_norm [upperProductsEffect]

end P256.Proofs.Field.Schoolbook
