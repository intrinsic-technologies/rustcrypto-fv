import P256.Proofs.HMAC.Interface
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.StoreByte
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
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

import P256.Proofs.HMAC.Finalize.Memory
import P256.Proofs.SHA256.Memory.Words

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

attribute [local x86_compose] movM8Imm8Effect

attribute [local x86_local] P256.Proofs.Common.Instructions.movM8Imm8Effect_local

structure OuterSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x100f21
  writable : Writable s (stackPtr s + 239) 41
  apart : RangeApart (stackPtr s + 239) 41 0x100f21 117

theorem OuterSetupPre.writableAt {s : RamState} (hp : OuterSetupPre s)
    (offset len : Nat) (hsub : offset + len ≤ 41) :
    Writable s (stackPtr s + BitVec.ofNat 64 (239 + offset)) len := by
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hp.writable.add offset hsub

theorem OuterSetupPre.apartAt {s : RamState} (hp : OuterSetupPre s)
    (offset len codeOffset codeLen : Nat) (hsub : offset + len ≤ 41)
    (hcode : codeOffset + codeLen ≤ 117) :
    RangeApart (stackPtr s + BitVec.ofNat 64 (239 + offset)) len
      (0x100f21 + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
    hp.apart (offset + i) (by omega) (codeOffset + j) (by omega)

def outerSetupBytes : List UInt8 :=
  [0x48, 0x89, 0xf3, 0x49, 0x89, 0xff, 0x4c, 0x8d, 0xb4, 0x24, 0xf0, 0x00, 0x00, 0x00, 0x48, 0xb8, 0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xb8, 0x7f, 0x52, 0x0e, 0x51, 0x8c, 0x68, 0x05, 0x9b, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8, 0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0xf8, 0x00, 0x00, 0x00, 0x48, 0xb8, 0x67, 0xe6, 0x09, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0x48, 0x89, 0x84, 0x24, 0xf0, 0x00, 0x00, 0x00, 0xc6, 0x84, 0x24, 0xef, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0xba, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0xfe]

def outerSetupEffect (s : RamState) : Effect :=
  { rip := 0x100f96
    writes := [
      ⟨(.reg 3 : Operand 64), s.regValue .rsi⟩,
      ⟨(.reg 15 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 240⟩,
      ⟨(.reg 0 : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 264) : Operand 64), 0x5be0cd191f83d9ab⟩,
      ⟨(.mem (stackPtr s + 256) : Operand 64), 0x9b05688c510e527f⟩,
      ⟨(.mem (stackPtr s + 248) : Operand 64), 0xa54ff53a3c6ef372⟩,
      ⟨(.mem (stackPtr s + 240) : Operand 64), 0xbb67ae856a09e667⟩,
      ⟨(.mem (stackPtr s + 239) : Operand 8), 0⟩,
      ⟨(.mem (stackPtr s + 272) : Operand 64), 1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 240⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rdi⟩] }

theorem outer_setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100f21 outerSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xf21 outerSetupBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem outer_setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OuterSetupPre (codeRange 0x100f21 outerSetupBytes)
      (Effect.post outerSetupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x100f21 0x48 0xf3 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf24 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100f24 0x49 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 3 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf27 (by decide))
  advance_then (lea_r64_effect_step 0x100f27 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 6 8
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2f (by decide))
  advance_then (mov_r64_imm64_effect_step 0x100f2f 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 14 10
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf39 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100f39 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 24 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writableAt 25 8 (by decide)
    · x86_norm
      exact hp.apartAt 25 8 24 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 25 8 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf41 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x100f41 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 32 10
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf4b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100f4b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 42 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writableAt 17 8 (by decide)
    · x86_norm
      exact hp.apartAt 17 8 42 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 17 8 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf53 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x100f53 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 50 10
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf5d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100f5d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 60 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writableAt 9 8 (by decide)
    · x86_norm
      exact hp.apartAt 9 8 60 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 9 8 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf65 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x100f65 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 68 10
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf6f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x100f6f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 78 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writableAt 1 8 (by decide)
    · x86_norm
      exact hp.apartAt 1 8 78 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 1 8 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf77 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x100f77 (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 86 8
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      have hw := hp.writableAt 0 1 (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · x86_norm
      exact hp.apartAt 0 1 86 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 0 1 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf7f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x100f7f 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 94 12
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writableAt 33 8 (by decide)
    · x86_norm
      exact hp.apartAt 33 8 94 12 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apartAt 33 8 0 117 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf8b (by decide))
  advance_then (mov_r32_imm32_effect_step 0x100f8b 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 106 5
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf90 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100f90 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 111 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf93 (by decide))
  advance_then (mov_r64_r64_effect_step 0x100f93 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100f21 outerSetupBytes 114 3
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf96 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [outerSetupEffect]
  · x86_norm [outerSetupEffect]
    all_goals (repeat' first | apply And.intro | (apply Or.inl; rfl) | apply Or.inr | rfl)
  · intro i; cases i <;> x86_norm [outerSetupEffect]
  · x86_norm [outerSetupEffect]
    all_goals (repeat' first | apply And.intro | (apply Or.inl; rfl) | apply Or.inr | rfl)

theorem outer_setup_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : HashCalleePre initial boundary entry 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) (rip : s.RIP = 0x100f21) :
    OuterSetupPre s := by
  refine ⟨rip, ?_, ?_⟩
  · exact ScalarFrame.stack_writable (stackPre pre) state (by decide) (by decide) (by decide)
  · exact ScalarFrame.stack_code (stackPre pre) state (by decide) (by decide)
      (codeOffset := 0xf21) (by decide)

theorem outer_setup_words {s t : RamState} (h : (outerSetupEffect s).Holds s t) :
    ∀ j < 4, memLoad t.external (stackPtr s + 240 + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]! := by
  have stores := h.writes
  simp only [outerSetupEffect, Write.AllHold, Operand.read] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.getElem!_cons_zero] using stores.2.2.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, List.getElem!_cons_zero, List.getElem!_cons_succ] using
      stores.2.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, List.getElem!_cons_zero, List.getElem!_cons_succ] using
      stores.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, List.getElem!_cons_zero, List.getElem!_cons_succ] using
      stores.2.2.2.2.1

theorem outer_setup_hash {s t : RamState} (hp : OuterSetupPre s)
    (h : (outerSetupEffect s).Holds s t) :
    SHA256.HashStateAt t (stackPtr s + 240) P256.Proofs.SHA256.initialHash := by
  refine ⟨by decide +kernel, ?_⟩
  intro j hj
  have read := ((hp.writableAt 1 32 (by decide)).of_holds h).mem
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := stackPtr s + 240 + BitVec.ofNat 64 (8*(j/2))) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read _ (by omega))
  rw [outer_setup_words h (j/2) (by omega)] at bytes
  have half := bytes.sub (4*(j%2)) 4 (by omega)
  have address : stackPtr s + 240 + BitVec.ofNat 64 (8*(j/2)) +
      BitVec.ofNat 64 (4*(j%2)) = stackPtr s + 240 + BitVec.ofNat 64 (4*j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address] at half
  apply SHA256.loadBytes32_of_bytes
  apply half.congr
  intro i hi
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem outer_setup_position {s t : RamState} (hp : OuterSetupPre s)
    (h : (outerSetupEffect s).Holds s t) :
    t.external[stackPtr s + 239]? = some 0 := by
  have stores := h.writes
  simp only [outerSetupEffect, Write.AllHold, Operand.read] at stores
  have word : memLoad t.external (stackPtr s + 239) 8 = 0 := stores.2.2.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 8) (a := stackPtr s + 239) ((hp.writableAt 0 1 (by decide)).of_holds h).mem
  rw [word] at bytes
  have byte := bytes 0 (by decide)
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using byte

theorem outer_setup_count {s t : RamState} (hp : OuterSetupPre s)
    (h : (outerSetupEffect s).Holds s t) :
    loadBytes t.external (stackPtr s + 272) 8 = .ok 1 := by
  have stores := h.writes
  simp only [outerSetupEffect, Write.AllHold, Operand.read] at stores
  have word : memLoad t.external (stackPtr s + 272) 64 = 1 := stores.2.2.2.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 64) (a := stackPtr s + 272) ((hp.writableAt 33 8 (by decide)).of_holds h).mem
  rw [word] at bytes
  exact bytes.loadBytes64

end P256.Proofs.HMAC.Finalize
