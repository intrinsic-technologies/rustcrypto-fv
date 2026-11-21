import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare.FirstCheck

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10da55
  readable : ∀ k < 4, MemReadable s (s.regValue .rbx + BitVec.ofNat 64 (8*k)) 8
  writable : ∀ offset ∈ ([0,8,16,24,128,136,144,152] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([0,8,16,24,128,136,144,152] : List Nat),
    ∀ codeOffset len : Nat, codeOffset + len ≤ 93 →
      RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
        (0x10da55 + BitVec.ofNat 64 codeOffset) len
  inputApart : ∀ k < 4, ∀ j < 4,
    RangeApart (rspOf s + BitVec.ofNat 64 (8*k)) 8
      (s.regValue .rbx + BitVec.ofNat 64 (8*j)) 8

theorem Pre.read_store {s : RamState} (h : Pre s)
    (mem : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [0,8,16,24]) (hd : d ∈ [0,8,16,24]) :
    memLoad (memStore mem ((Operand.reg 4#5 : Operand 64).read s + c) v)
      ((Operand.reg 3#5 : Operand 64).read s + d) 64 =
      memLoad mem ((Operand.reg 3#5 : Operand 64).read s + d) 64 := by
  have hc' : c ∈ List.ofFn (fun k : Fin 4 => BitVec.ofNat 64 (8*k.val)) := hc
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc'
  have hd' : d ∈ List.ofFn (fun j : Fin 4 => BitVec.ofNat 64 (8*j.val)) := hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd'
  exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart mem _ _ v 64
    (h.inputApart k.val k.isLt j.val j.isLt)

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x43, 0x18, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x43, 0x10, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x3, 0x48, 0x8b, 0x4b, 0x8, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0xc7, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xe7, 0x48, 0x8d, 0xb4, 0x24, 0x80, 0x0, 0x0, 0x0]

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xda55 93 = bytes := by
  decide +kernel

def effect (s : RamState) : Effect :=
  { rip := 0x10dab2
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (s.regValue .rbx) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (s.regValue .rbx+8) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+0⟩,
      ⟨(.reg 6 : Operand 64), rspOf s+128⟩,
      ⟨(.mem (rspOf s+0) : Operand 64), (.mem (s.regValue .rbx+0) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+8) : Operand 64), (.mem (s.regValue .rbx+8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+16) : Operand 64), (.mem (s.regValue .rbx+16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+24) : Operand 64), (.mem (s.regValue .rbx+24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+128) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+136) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+144) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s+152) : Operand 64), 0⟩
    ] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 93, (0x10da55 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10da55 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10da55 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 3 (by decide)⟩
  case next =>
    intro _ _
    exact outside 4 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10da59 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 4 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 9 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10da5e 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 9 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 13 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10da62 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 13 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 18 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10da67 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 21 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10da6a 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 21 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 25 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10da6e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 25 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 30 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10da73 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 30 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 30 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 34 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10da77 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 34 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 34 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 46 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10da83 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 46 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 46 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 58 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10da8f 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 58 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 58 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 70 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10da9b 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 70 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 70 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0 93 (by decide)
    · x86_norm
      exact outside 82 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10daa7 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 82 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 85 (by decide)
  advance_then (lea_r64_effect_step 0x10daaa 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10da55 bytes 85 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 93 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, hP.read_store]
    simp only [BitVec.add_zero]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Core.Prepare.FirstCheck
