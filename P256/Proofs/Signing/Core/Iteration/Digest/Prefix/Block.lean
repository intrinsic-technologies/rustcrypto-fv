import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.StoreByte

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Prefix.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cbed
  readable : ∀ offset ∈ ([8, 16, 24, 32, 88, 96] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([528, 1328, 1336, 1344, 1352, 432, 304, 312, 320, 328] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([528, 1328, 1336, 1344, 1352, 432, 304, 312, 320, 328] : List Nat),
    ∀ codeOffset len : Nat, codeOffset + len ≤ 167 →
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cbed + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x8c, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x30, 0x1, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x1, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x0, 0xc7, 0x84, 0x24, 0xb0, 0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x48, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x40, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x38, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x30, 0x5, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xb9, 0x4, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x7c, 0x24, 0x58, 0x48, 0x8b, 0x74, 0x24, 0x60, 0x4c, 0x89, 0xfa, 0x41, 0xb8, 0x0, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10cc94
    writes := [
      ⟨(.reg 0 : Operand 64), (Operand.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 7 : Operand 64), (Operand.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 8 : Operand 64), 256⟩,
      ⟨(.mem (rspOf s + 304) : Operand 64), (Operand.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 312) : Operand 64), (Operand.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 320) : Operand 64), (Operand.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), (Operand.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 528) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s + 432) : Operand 32), 256⟩,
      ⟨(.mem (rspOf s + 1328) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1336) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1344) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 1352) : Operand 64), 0⟩] }

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] P256.Proofs.Common.Instructions.movM8Imm8Effect_local

theorem writable_narrow {s : RamState} {a : BitVec 64} {len : Nat}
    (h : MemWritable s a 8) (bound : len ≤ 8) : MemWritable s a len := by
  exact ⟨by have := h.low; omega,
    fun i hi => h.mem i (by omega), h.tables.sub (by omega) (by omega)⟩

theorem read_store (s : RamState) (m : Ram) (c d : BitVec 64) {n : Nat} (v : BitVec n)
    (hc : c ∈ [528, 1328, 1336, 1344, 1352, 432, 304, 312, 320, 328])
    (hd : d ∈ [8, 16, 24, 32, 88, 96]) (hn : n ≤ 64) :
    memLoad (memStore m (rspOf s + c) v) (rspOf s + d) 64 =
      memLoad m (rspOf s + d) 64 := by
  have apart : RangeApart (rspOf s + c) 8 (rspOf s + d) 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply RangeApart.offsets (rspOf s) (by decide) (by decide)
    all_goals first | exact .inl (by decide) | exact .inr (by decide)
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi
  exact apart i (by omega) j hj

theorem write_mem_external (s : RamState) (a : BitVec 64) {n : Nat} (v : BitVec n) :
    ((Operand.mem a : Operand n).write s v).external = memStore s.external a v := rfl

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 167, (0x10cbed : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cbed bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10cbed 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 32 (by simp)⟩
  case next =>
    intro _ _
    exact outside 5 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbf2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 328 (by simp)
    · x86_norm
      exact hP.codeApart 328 (by simp) 5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 328 (by simp) 0 167 (by decide)
    · exact outside 13 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cbfa 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 18 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbff 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 320 (by simp)
    · x86_norm
      exact hP.codeApart 320 (by simp) 18 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 320 (by simp) 0 167 (by decide)
    · exact outside 26 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cc07 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 31 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cc0c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 31 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 36 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cc11 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 312 (by simp)
    · x86_norm
      exact hP.codeApart 312 (by simp) 36 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 312 (by simp) 0 167 (by decide)
    · exact outside 44 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cc19 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 304 (by simp)
    · x86_norm
      exact hP.codeApart 304 (by simp) 44 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 304 (by simp) 0 167 (by decide)
    · exact outside 52 (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10cc21 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 1)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact writable_narrow (hP.writable 528 (by simp)) (by decide)
    · x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 52 8 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 0 167 (by decide) i (by omega) j hj
    · exact outside 60 (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10cc29 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 60 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact writable_narrow (hP.writable 528 (by simp)) (by decide)
    · x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 60 8 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 0 167 (by decide) i (by omega) j hj
    · exact outside 68 (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10cc31 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 68 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact writable_narrow (hP.writable 528 (by simp)) (by decide)
    · x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 68 8 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 0 167 (by decide) i (by omega) j hj
    · exact outside 76 (by decide)
  advance_then (mov_m8_imm8_effect_step 0x10cc39 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 76 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact writable_narrow (hP.writable 528 (by simp)) (by decide)
    · x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 76 8 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.codeApart 528 (by simp) 0 167 (by decide) i (by omega) j hj
    · exact outside 84 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_imm32_legacy_effect_step_any 0x10cc41 (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl 256)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 84 11
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      have hw := writable_narrow (hP.writable 432 (by simp)) (len := 4) (by decide)
      exact ⟨hw.readable, hw.tables⟩
    · x86_norm
      intro i hi j hj
      exact hP.codeApart 432 (by simp) 84 11 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.codeApart 432 (by simp) 0 167 (by decide) i (by omega) j hj
    · exact outside 95 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cc4c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 95 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1352 (by simp)
    · x86_norm
      exact hP.codeApart 1352 (by simp) 95 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1352 (by simp) 0 167 (by decide)
    · exact outside 107 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cc58 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1344)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 107 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1344 (by simp)
    · x86_norm
      exact hP.codeApart 1344 (by simp) 107 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1344 (by simp) 0 167 (by decide)
    · exact outside 119 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cc64 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 119 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1336 (by simp)
    · x86_norm
      exact hP.codeApart 1336 (by simp) 119 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1336 (by simp) 0 167 (by decide)
    · exact outside 131 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10cc70 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 1328)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 131 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1328 (by simp)
    · x86_norm
      exact hP.codeApart 1328 (by simp) 131 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1328 (by simp) 0 167 (by decide)
    · exact outside 143 (by decide)
  advance_then (mov_r32_imm32_effect_step 0x10cc7c 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 143 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 148 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cc81 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 148 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 153 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cc86 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 153 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 158 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cc8b 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 158 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 161 (by decide)
  advance_then (mov_r32_imm32_rex_effect_step 0x10cc8e 0x41 0xb8 (by simp [RexNoWPrefix]) (by decide +kernel) 256)
  case sub => exact codeRange_slice_subset 0x10cbed bytes 161 6
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 167 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, read_store, write_mem_external,
      P256.Proofs.Verifying.Core.Scalars.operand_write_reg_external]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Digest.Prefix.Block
