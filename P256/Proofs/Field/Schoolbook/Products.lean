import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Field.Schoolbook.Frame

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulFlags64 mulHigh64 mul_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Common.Field
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def productsBytes : List UInt8 :=
  [0x4c, 0x8b, 0x1, 0x4c, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x59, 0x8, 0x4c, 0x8b, 0x49, 0x10,
    0x4c, 0x8b, 0x36, 0x4c, 0x8b, 0x56, 0x8, 0x48, 0x89, 0x74, 0x24, 0x8, 0x48, 0x89, 0xd8, 0x48,
    0x89, 0x5c, 0x24, 0x48, 0x49, 0xf7, 0xe2, 0x49, 0x89, 0xd3, 0x48, 0x89, 0x4, 0x24, 0x4c, 0x89,
    0xc0, 0x49, 0xf7, 0xe2, 0x48, 0x89, 0xd6, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x89, 0xd8, 0x49,
    0xf7, 0xe6, 0x49, 0x89, 0xc4, 0x49, 0x89, 0xd5, 0x48, 0x8b, 0x59, 0x18, 0x4c, 0x89, 0xc0, 0x49,
    0xf7, 0xe6, 0x49, 0x89, 0xd0, 0x48, 0x89, 0x44, 0x24, 0x50, 0x4c, 0x89, 0xc8, 0x49, 0xf7, 0xe6,
    0x48, 0x89, 0xd5, 0x49, 0x89, 0xc7, 0x48, 0x89, 0xd8, 0x49, 0xf7, 0xe6, 0x48, 0x89, 0xc1, 0x48,
    0x89, 0x54, 0x24, 0x10]

structure ProductsPre (s : RamState) : Prop extends
    ScratchPre 0x11c982 productsBytes.length s where
  left : MemReadable s ((Operand.reg 6 : Operand 64).read s) 32
  right : MemReadable s ((Operand.reg 1 : Operand 64).read s) 32
  leftApart : RangeApart (rspOf s) 88 ((Operand.reg 6 : Operand 64).read s) 32
  rightApart : RangeApart (rspOf s) 88 ((Operand.reg 1 : Operand 64).read s) 32

theorem products_readable_slice {s : RamState} {a : BitVec 64}
    (h : MemReadable s a 32) (offset : Nat) (bound : offset + 8 ≤ 32) :
    MemReadable s (a + BitVec.ofNat 64 offset) 8 := by
  refine ⟨?_, ?_⟩
  · have := h.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h.mem (offset+i) (by omega)

theorem products_apart_slice {a b c d : BitVec 64} {n m : Nat}
    (apart : RangeApart a n b m) (hc : c.toNat + 8 ≤ n) (hd : d.toNat + 8 ≤ m) :
    RangeApart (a + c) 8 (b + d) 8 := by
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using
    apart (c.toNat + i) (by omega) (d.toNat + j) (by omega)

theorem products_load_store {a b : BitVec 64} (apart : RangeApart a 88 b 32)
    (mem : Ram) (c d v : BitVec 64) (hc : c.toNat + 8 ≤ 88) (hd : d.toNat + 8 ≤ 32) :
    memLoad (memStore mem (a+c) v) (b+d) 64 = memLoad mem (b+d) 64 :=
  memLoad_memStore_rangeApart mem (a+c) (b+d) v 64 (products_apart_slice apart hc hd)

theorem products_load_store_left {a b : BitVec 64} (apart : RangeApart a 88 b 32)
    (mem : Ram) (d v : BitVec 64) (hd : d.toNat + 8 ≤ 32) :
    memLoad (memStore mem a v) (b+d) 64 = memLoad mem (b+d) 64 := by
  have h := products_load_store apart mem 0#64 d v (by decide) hd
  rw [BitVec.add_zero] at h
  exact h

theorem products_load_store_right {a b : BitVec 64} (apart : RangeApart a 88 b 32)
    (mem : Ram) (c v : BitVec 64) (hc : c.toNat + 8 ≤ 88) :
    memLoad (memStore mem (a+c) v) b 64 = memLoad mem b 64 := by
  have h := products_load_store apart mem c 0#64 v hc (by decide)
  rw [BitVec.add_zero] at h
  exact h

def productsLoadsEffect (s : RamState) : Effect :=
  let a0 := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s
  let a1 := (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s
  let b0 := (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
  let b1 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 8) : Operand 64).read s
  let b2 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 16) : Operand 64).read s
  { rip := 0x11c9a6
    writes := [
      ⟨(Operand.reg 0 : Operand 64), b1⟩,
      ⟨(Operand.reg 3 : Operand 64), b1⟩,
      ⟨(Operand.reg 8 : Operand 64), b0⟩,
      ⟨(Operand.reg 9 : Operand 64), b2⟩,
      ⟨(Operand.reg 10 : Operand 64), a1⟩,
      ⟨(Operand.reg 14 : Operand 64), a0⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 64) : Operand 64), b0⟩,
      ⟨(Operand.mem (rspOf s + 72) : Operand 64), b1⟩] }

def productsCrossEffect (s : RamState) : Effect :=
  let a0 := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s
  let a1 := (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s
  let b0 := (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
  let b1 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 8) : Operand 64).read s
  let b2 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 16) : Operand 64).read s
  { rip := 0x11c9ca
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (b1 * a0)⟩,
      ⟨(Operand.reg 2 : Operand 64), (mulHigh64 b1 a0)⟩,
      ⟨(Operand.reg 3 : Operand 64), b1⟩,
      ⟨(Operand.reg 6 : Operand 64), (mulHigh64 b0 a1)⟩,
      ⟨(Operand.reg 8 : Operand 64), b0⟩,
      ⟨(Operand.reg 9 : Operand 64), b2⟩,
      ⟨(Operand.reg 10 : Operand 64), a1⟩,
      ⟨(Operand.reg 11 : Operand 64), (mulHigh64 b1 a1)⟩,
      ⟨(Operand.reg 12 : Operand 64), (b1 * a0)⟩,
      ⟨(Operand.reg 13 : Operand 64), (mulHigh64 b1 a0)⟩,
      ⟨(Operand.reg 14 : Operand 64), a0⟩,
      ⟨(Operand.mem (rspOf s) : Operand 64), (b1 * a1)⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 24) : Operand 64), (b0 * a1)⟩,
      ⟨(Operand.mem (rspOf s + 64) : Operand 64), b0⟩,
      ⟨(Operand.mem (rspOf s + 72) : Operand 64), b1⟩]
    flags := some (mulFlags64 b1 a0) }

def productsEffect (s : RamState) : Effect :=
  let a0 := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s
  let a1 := (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s
  let b0 := (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
  let b1 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 8) : Operand 64).read s
  let b2 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 16) : Operand 64).read s
  let b3 := (Operand.mem ((Operand.reg 1 : Operand 64).read s + 24) : Operand 64).read s
  { rip := 0x11c9f6
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (b3 * a0)⟩,
      ⟨(Operand.reg 1 : Operand 64), (b3 * a0)⟩,
      ⟨(Operand.reg 2 : Operand 64), (mulHigh64 b3 a0)⟩,
      ⟨(Operand.reg 3 : Operand 64), b3⟩,
      ⟨(Operand.reg 5 : Operand 64), (mulHigh64 b2 a0)⟩,
      ⟨(Operand.reg 6 : Operand 64), (mulHigh64 b0 a1)⟩,
      ⟨(Operand.reg 8 : Operand 64), (mulHigh64 b0 a0)⟩,
      ⟨(Operand.reg 9 : Operand 64), b2⟩,
      ⟨(Operand.reg 10 : Operand 64), a1⟩,
      ⟨(Operand.reg 11 : Operand 64), (mulHigh64 b1 a1)⟩,
      ⟨(Operand.reg 12 : Operand 64), (b1 * a0)⟩,
      ⟨(Operand.reg 13 : Operand 64), (mulHigh64 b1 a0)⟩,
      ⟨(Operand.reg 14 : Operand 64), a0⟩,
      ⟨(Operand.reg 15 : Operand 64), (b2 * a0)⟩,
      ⟨(Operand.mem (rspOf s) : Operand 64), (b1 * a1)⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 16) : Operand 64), (mulHigh64 b3 a0)⟩,
      ⟨(Operand.mem (rspOf s + 24) : Operand 64), (b0 * a1)⟩,
      ⟨(Operand.mem (rspOf s + 64) : Operand 64), b0⟩,
      ⟨(Operand.mem (rspOf s + 72) : Operand 64), b1⟩,
      ⟨(Operand.mem (rspOf s + 80) : Operand 64), (b0 * a0)⟩]
    flags := some (mulFlags64 b3 a0) }

attribute [x86_compose] productsLoadsEffect productsCrossEffect

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2048 in
theorem products_loads_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsLoadsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11c982 0x4c
    (by simp [RexWPrefix]) 0 (.base 1 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact products_readable_slice hP.right 0 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1c985 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c985 0x4c
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 3 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 64 (by decide)
      · x86_norm
        exact hf.apart 64 (by decide) 3 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c98a (by decide))
  advance_then (mov_r64_m64_effect_step 0x11c98a 0x48
    (by simp [RexWPrefix]) 3 (.base 1 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 8 4
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      exact products_readable_slice hP.right 8 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c98e (by decide))
  advance_then (mov_r64_m64_effect_step 0x11c98e 0x4c
    (by simp [RexWPrefix]) 1 (.base 1 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 12 4
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      exact products_readable_slice hP.right 16 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c992 (by decide))
  advance_then (mov_r64_m64_effect_step 0x11c992 0x4c
    (by simp [RexWPrefix]) 6 (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 16 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      exact products_readable_slice hP.left 0 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c995 (by decide))
  advance_then (mov_r64_m64_effect_step 0x11c995 0x4c
    (by simp [RexWPrefix]) 2 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 19 4
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      exact products_readable_slice hP.left 8 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c999 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c999 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 23 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 8 (by decide)
      · x86_norm
        exact hf.apart 8 (by decide) 23 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c99e (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c99e 0x48 0xd8
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 28 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9a1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c9a1 0x48
    (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 31 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 72 (by decide)
      · x86_norm
        exact hf.apart 72 (by decide) 31 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9a6 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hl := hP.leftApart
  have hr := hP.rightApart
  x86_norm at hl hr
  apply hH.weaken
  · x86_norm [productsLoadsEffect]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsLoadsEffect, BitVec.add_zero, products_load_store hl, products_load_store hr, products_load_store_right hl]
    all_goals (try (repeat constructor <;> rfl))
  · intro i; cases i <;> simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsLoadsEffect]
    all_goals (try (repeat constructor <;> rfl))
  · x86_norm [productsLoadsEffect, BitVec.add_zero]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2048 in
theorem products_cross_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsLoadsEffect) →
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsCrossEffect) := by
  advance_then (mul_r64_effect_step 0x11c9a6 0x49 0xe2
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 36 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [productsLoadsEffect])
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9a9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9a9 0x49 0xd3
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 39 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9ac (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c9ac 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 42 4
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 0 (by decide)
      · x86_norm
        exact hf.apart 0 (by decide) 42 4 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9b0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9b0 0x4c 0xc0
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 46 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9b3 (by decide))
  advance_then (mul_r64_effect_step 0x11c9b3 0x49 0xe2
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 49 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9b6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9b6 0x48 0xd6
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 52 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9b9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c9b9 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 55 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 24 (by decide)
      · x86_norm
        exact hf.apart 24 (by decide) 55 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9be (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9be 0x48 0xd8
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 60 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9c1 (by decide))
  advance_then (mul_r64_effect_step 0x11c9c1 0x49 0xe6
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 63 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9c4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9c4 0x49 0xc4
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 66 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9c7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9c7 0x49 0xd5
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 69 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9ca (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [productsCrossEffect]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsCrossEffect, BitVec.add_zero]
    all_goals (try (repeat constructor <;> rfl))
  · intro i; cases i <;> simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsCrossEffect]
    all_goals (try (repeat constructor <;> rfl))
  · x86_norm [productsCrossEffect, BitVec.add_zero]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2048 in
theorem products_finish_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsCrossEffect) →
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsEffect) := by
  advance_then (mov_r64_m64_effect_step 0x11c9ca 0x48
    (by simp [RexWPrefix]) 3 (.base 1 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 72 4
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [productsCrossEffect]) (by x86_addr_obs) ?_
      x86_norm [productsCrossEffect]
      exact products_readable_slice hP.right 24 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9ce (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9ce 0x4c 0xc0
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 76 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9d1 (by decide))
  advance_then (mul_r64_effect_step 0x11c9d1 0x49 0xe6
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 79 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9d4 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9d4 0x49 0xd0
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 82 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9d7 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c9d7 0x48
    (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 85 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 80 (by decide)
      · x86_norm
        exact hf.apart 80 (by decide) 85 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9dc (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9dc 0x4c 0xc8
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 90 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9df (by decide))
  advance_then (mul_r64_effect_step 0x11c9df 0x49 0xe6
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 93 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9e2 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9e2 0x48 0xd5
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 96 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9e5 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9e5 0x49 0xc7
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 99 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9e8 (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9e8 0x48 0xd8
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 102 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9eb (by decide))
  advance_then (mul_r64_effect_step 0x11c9eb 0x49 0xe6
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 105 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9ee (by decide))
  advance_then (mov_r64_r64_effect_step 0x11c9ee 0x48 0xc1
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 108 3
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9f1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x11c9f1 0x48
    (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11c982 productsBytes 111 5
  case mid =>
    intro s t hP hH hO
    have hf := hP.toScratchPre
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hf.writable 16 (by decide)
      · x86_norm
        exact hf.apart 16 (by decide) 111 5 (by decide)
    · schoolbook_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1c9f6 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hr := hP.rightApart
  x86_norm at hr
  apply hH.weaken
  · x86_norm [productsEffect]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsEffect, products_load_store hr, products_load_store_left hr]
    all_goals (try (repeat constructor <;> rfl))
  · intro i; cases i <;> simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, productsEffect, products_load_store hr, products_load_store_left hr]
    all_goals (try (repeat constructor <;> rfl))
  · x86_norm [productsEffect, BitVec.add_zero]

theorem products_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ProductsPre (codeRange 0x11c982 productsBytes)
      (Effect.post productsEffect) :=
  products_finish_correct boundary hout
    (products_cross_correct boundary hout (products_loads_correct boundary hout))

theorem products_bytes :
    Extracted.textBytes.toListFrom 0x1c982 productsBytes.length = productsBytes := by
  decide +kernel

theorem products_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11c982 productsBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1c982 productsBytes
    (by decide) products_bytes

end P256.Proofs.Field.Schoolbook
