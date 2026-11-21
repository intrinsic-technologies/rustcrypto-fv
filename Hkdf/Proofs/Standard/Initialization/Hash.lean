import Hkdf.Proofs.Standard.Initialization.Layout
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Key.Hash.Initialize.Payload
import Hkdf.Proofs.Common.Memory.Pointers

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.SHA256

structure InnerState [Bindings] (initial s : RamState) (salt : Option ByteArray) : Prop
    extends Standard.Preserved initial s where
  innerHash : HashStateAt s (frameBase initial + 56)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
      (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36))
  innerBlocks : loadBytes s.external (frameBase initial + 88) 8 = .ok 1
  ivRegisters : s.regValue .rbx = 0x5be0cd191f83d9ab ∧
    s.regValue .r14 = 0x9b05688c510e527f ∧
    s.regValue .r12 = 0xa54ff53a3c6ef372 ∧ s.regValue .r13 = 0xbb67ae856a09e667

structure InnerHashed [Bindings] (initial s : RamState) (salt : Option ByteArray) : Prop
    extends InnerState initial s salt where
  rip : s.RIP = 0x10150b
  block : (⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36)

structure OuterReady [Bindings] (initial s : RamState) (salt : Option ByteArray) : Prop
    extends InnerState initial s salt where
  rip : s.RIP = 0x10152e
  block : (⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x5c)

open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def ivWords : List (BitVec 64) :=
  [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab]

theorem iv_loaded {s : RamState} (loaded : ProgramLoaded s) :
    ∀ j < 4, MemReadable s (0x200ee0 + BitVec.ofNat 64 (8*j)) 8 ∧
      memLoad s.external (0x200ee0 + BitVec.ofNat 64 (8*j)) 64 = ivWords[j]! := by
  intro j hj
  have bytes : ∀ i : Fin 8,
      Extracted.rodataBytes.toList[3808 + 8*j + i.val]'(by
        rw [chunked_toList_length, rodataBytes_size]; omega) =
          storedByte (ivWords[j]!) i.val := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    all_goals decide +kernel +revert
  have stored : Bytes s.external (0x200ee0 + BitVec.ofNat 64 (8*j)) 8
      (storedByte (ivWords[j]!)) := by
    intro i hi
    have byte := Hkdf.Proofs.Common.Memory.rodata_loaded loaded
      (offset := 3808 + 8*j + i) (by omega)
    rw [bytes ⟨i, hi⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  have bound : (0x200ee0 + BitVec.ofNat 64 (8*j) : BitVec 64).toNat + 8 < 2^32 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    all_goals decide
  exact ⟨stored.readable (Nat.le_of_lt bound), stored.memLoad (by decide) (by decide)⟩

structure InnerPre (s : RamState) : Prop where
  rip : s.RIP = 0x1014be
  readable : ∀ j < 4, MemReadable s (0x200ee0 + BitVec.ofNat 64 (8*j)) 8
  writable : ∀ offset ∈ ([80,72,64,56,88] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([80,72,64,56,88] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 0x1014be 72
  rodata : ∀ (m : Ram) (v : BitVec 64) (offset : Nat),
    offset ∈ ([80,72,64,56,88] : List Nat) → ∀ j < 4,
    memLoad (memStore m (rspOf s + BitVec.ofNat 64 offset) v)
      (0x200ee0 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad m (0x200ee0 + BitVec.ofNat 64 (8*j)) 64

def innerBytes : List UInt8 :=

  [0x48,0x8b,0x1d,0x33,0xfa,0xf,0x0,0x48,0x89,0x5c,0x24,0x50,0x4c,0x8b,0x35,0x1f,0xfa,0xf,0x0,0x4c,0x89,0x74,0x24,0x48,0x4c,0x8b,0x25,0xb,0xfa,0xf,0x0,0x4c,0x89,0x64,0x24,0x40,0x4c,0x8b,0x2d,0xf7,0xf9,0xf,0x0,0x4c,0x89,0x6c,0x24,0x38,0x48,0xc7,0x44,0x24,0x58,0x1,0x0,0x0,0x0,0x48,0x8d,0x7c,0x24,0x38,0x48,0x8d,0x74,0x24,0x78,0xba,0x1,0x0,0x0,0x0]

def innerEffect (s : RamState) : Effect :=
  { rip := 0x101506
    writes := [
      ⟨(.reg 3 : Operand 64), memLoad s.external 0x200ef8 64⟩,
      ⟨(.reg 14 : Operand 64), memLoad s.external 0x200ef0 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external 0x200ee8 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external 0x200ee0 64⟩,
      ⟨(.mem (rspOf s + 80) : Operand 64), memLoad s.external 0x200ef8 64⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), memLoad s.external 0x200ef0 64⟩,
      ⟨(.mem (rspOf s + 64) : Operand 64), memLoad s.external 0x200ee8 64⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), memLoad s.external 0x200ee0 64⟩,
      ⟨(.mem (rspOf s + 88) : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 56⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] }

set_option maxHeartbeats 1200000 in
theorem inner_stage_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InnerPre (codeRange 0x1014be innerBytes)
      (Effect.post innerEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1014be 0x48 (by simp [RexWPrefix]) 3 (.rip 0xffa33) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, by x86_norm; simpa using h.readable 3 (by decide)⟩
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x14c5 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1014c5 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 7 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 80 (by simp) a ha (7+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 80 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14ca (by decide))
  advance_then (mov_r64_m64_effect_step 0x1014ca 0x4c (by simp [RexWPrefix]) 6 (.rip 0xffa1f) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 12 7)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa using hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14d1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1014d1 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 19 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 72 (by simp) a ha (19+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14d6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1014d6 0x4c (by simp [RexWPrefix]) 4 (.rip 0xffa0b) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 24 7)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa using hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14dd (by decide))
  advance_then (mov_m64_r64_effect_step 0x1014dd 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 31 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 64 (by simp) a ha (31+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14e2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1014e2 0x4c (by simp [RexWPrefix]) 5 (.rip 0xff9f7) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 36 7)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa using hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14e9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1014e9 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 43 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 56 (by simp) a ha (43+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14ee (by decide))
  advance_then (mov_m64_imm32_effect_step 0x1014ee 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 48 9)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 88 (by simp) a ha (48+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14f7 (by decide))
  advance_then (lea_r64_effect_step 0x1014f7 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 57 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x14fc (by decide))
  advance_then (lea_r64_effect_step 0x1014fc 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 62 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1501 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x101501 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x1014be innerBytes 67 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1506 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have skip0 (m : Ram) (v : BitVec 64) (offset : Nat)
      (member : offset ∈ ([80,72,64,56,88] : List Nat)) := hp.rodata m v offset member 0 (by decide)
  have skip1 (m : Ram) (v : BitVec 64) (offset : Nat)
      (member : offset ∈ ([80,72,64,56,88] : List Nat)) := hp.rodata m v offset member 1 (by decide)
  have skip2 (m : Ram) (v : BitVec 64) (offset : Nat)
      (member : offset ∈ ([80,72,64,56,88] : List Nat)) := hp.rodata m v offset member 2 (by decide)
  have skip3 (m : Ram) (v : BitVec 64) (offset : Nat)
      (member : offset ∈ ([80,72,64,56,88] : List Nat)) := hp.rodata m v offset member 3 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] at skip0 skip1 skip2 skip3
  have skip2_80 (m : Ram) (v : BitVec 64) := skip2 m v 80 (by simp)
  have skip1_80 (m : Ram) (v : BitVec 64) := skip1 m v 80 (by simp)
  have skip1_72 (m : Ram) (v : BitVec 64) := skip1 m v 72 (by simp)
  have skip0_80 (m : Ram) (v : BitVec 64) := skip0 m v 80 (by simp)
  have skip0_72 (m : Ram) (v : BitVec 64) := skip0 m v 72 (by simp)
  have skip0_64 (m : Ram) (v : BitVec 64) := skip0 m v 64 (by simp)
  simp only [rspOf, Operand.read] at skip2_80 skip1_80 skip1_72 skip0_80 skip0_72 skip0_64
  simp only [BitVec.ofNat_eq_ofNat] at skip2_80 skip1_80 skip1_72 skip0_80 skip0_72 skip0_64
  apply hh.weaken
  · x86_norm [innerEffect, Operand.write]
    all_goals simp only [Operand.read, skip2_80, skip1_80, skip1_72, skip0_80, skip0_72, skip0_64]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [innerEffect, Operand.write]
    all_goals simp only [Operand.read, skip2_80, skip1_80, skip1_72, skip0_80, skip0_72, skip0_64]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [innerEffect]
  · x86_norm [innerEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

structure OuterPre (s : RamState) : Prop where
  rip : s.RIP = 0x10152e
  writable : ∀ offset ∈ ([40,32,24,16,48] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([40,32,24,16,48] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 0x10152e 44

def outerBytes : List UInt8 :=
  [0x48,0x89,0x5c,0x24,0x28,0x4c,0x89,0x74,0x24,0x20,0x4c,0x89,0x64,0x24,0x18,0x4c,0x89,0x6c,0x24,0x10,0x48,0xc7,0x44,0x24,0x30,0x1,0x0,0x0,0x0,0x48,0x8d,0x7c,0x24,0x10,0x48,0x8d,0x74,0x24,0x78,0xba,0x1,0x0,0x0,0x0]

def outerEffect (s : RamState) : Effect :=
  { rip := 0x10155a
    writes := [
      ⟨(.mem (rspOf s + 40) : Operand 64), s.regValue .rbx⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), s.regValue .r14⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), s.regValue .r12⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), s.regValue .r13⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 16⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 2 : Operand 64), 1⟩] }

set_option maxHeartbeats 900000 in
theorem outer_stage_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OuterPre (codeRange 0x10152e outerBytes)
      (Effect.post outerEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10152e 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 40 (by simp), ?_⟩
    intro a ha b hb
    exact h.codeApart 40 (by simp) a ha b (by simp [AddrMode.tail, Disp.bytes, immBytes] at hb ⊢; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 40 (by simp)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1533 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101533 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 32 (by simp) a ha (5+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1538 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101538 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 10 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 24 (by simp) a ha (10+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x153d (by decide))
  advance_then (mov_m64_r64_effect_step 0x10153d 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 15 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 16 (by simp) a ha (15+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1542 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x101542 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 20 9)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart 48 (by simp) a ha (20+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x154b (by decide))
  advance_then (lea_r64_effect_step 0x10154b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 29 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1550 (by decide))
  advance_then (lea_r64_effect_step 0x101550 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 34 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1555 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x101555 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10152e outerBytes 39 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x155a (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [outerEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [outerEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [outerEffect]
  · x86_norm [outerEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

