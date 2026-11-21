import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare.SecondCheck.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10db01
  readable15 : ∀ offset ∈ ([32, 40, 48, 56] : List Nat), MemReadable s ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([0, 8, 16, 24, 128, 136, 144, 152] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([0, 8, 16, 24, 128, 136, 144, 152] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 94 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10db01 + BitVec.ofNat 64 codeOffset) len
  inputApart : ∀ offset ∈ ([0, 8, 16, 24, 128, 136, 144, 152] : List Nat), ∀ inputOffset ∈ ([32, 40, 48, 56] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 inputOffset) 8

theorem Pre.read_store {s : RamState} (h : Pre s) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [0, 8, 16, 24, 128, 136, 144, 152]) (hd : d ∈ [32, 40, 48, 56]) :
    memLoad (memStore m ((Operand.reg 4#5 : Operand 64).read s + c) v) ((Operand.reg 3#5 : Operand 64).read s + d) 64 =
      memLoad m ((Operand.reg 3#5 : Operand 64).read s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (h.inputApart _ (by simp) _ (by simp))

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x43, 0x38, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x43, 0x30, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x43, 0x20, 0x48, 0x8b, 0x4b, 0x28, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0xc7, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xe7, 0x48, 0x8d, 0xb4, 0x24, 0x80, 0x0, 0x0, 0x0]

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xdb01 94 = bytes := by
  decide +kernel

def effect (s : RamState) : Effect :=
  { rip := 0x10db5f
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 32) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 40) : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), rspOf s + 128⟩,
      ⟨(Operand.reg 7 : Operand 64), rspOf s + 0⟩,
      ⟨(Operand.mem (rspOf s + 0) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 32) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 8) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 40) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 16) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 48) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 24) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 56) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 128) : Operand 64), 0⟩,
      ⟨(Operand.mem (rspOf s + 136) : Operand 64), 0⟩,
      ⟨(Operand.mem (rspOf s + 144) : Operand 64), 0⟩,
      ⟨(Operand.mem (rspOf s + 152) : Operand 64), 0⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 94, (0x10db01 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10db01 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10db01 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 56)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable15 56 (by simp)⟩
  case next =>
    intro _ _
    exact outside 4 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db05 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 4 5
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
      exact hP.codeApart 24 (by simp) 0 94 (by decide)
    · exact outside 9 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db0a 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 13 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db0e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 13 5
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
      exact hP.codeApart 16 (by simp) 0 94 (by decide)
    · exact outside 18 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db13 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 22 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db17 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 26 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db1b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 26 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0 94 (by decide)
    · exact outside 31 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db20 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 31 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 31 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0 94 (by decide)
    · exact outside 35 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10db24 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 35 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 35 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0 94 (by decide)
    · exact outside 47 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10db30 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 47 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 47 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0 94 (by decide)
    · exact outside 59 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10db3c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 59 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 59 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0 94 (by decide)
    · exact outside 71 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10db48 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 71 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 71 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0 94 (by decide)
    · exact outside 83 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10db54 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 83 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 86 (by decide)
  advance_then (lea_r64_effect_step 0x10db57 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db01 bytes 86 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 94 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, hP.read_store]
    all_goals try simp only [BitVec.add_zero]
    all_goals repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Core.Prepare.SecondCheck.Block
