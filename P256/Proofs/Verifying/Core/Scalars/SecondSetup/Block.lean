import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars.SecondSetup.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10dd1d
  readable15 : ∀ offset ∈ ([0, 8, 16, 24] : List Nat), MemReadable s ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 71 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10dd1d + BitVec.ofNat 64 codeOffset) len
  inputApart : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), ∀ inputOffset ∈ ([0, 8, 16, 24] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 inputOffset) 8

theorem Pre.read_store {s : RamState} (h : Pre s) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [128, 136, 144, 152]) (hd : d ∈ [0, 8, 16, 24]) :
    memLoad (memStore m ((Operand.reg 4#5 : Operand 64).read s + c) v) ((Operand.reg 3#5 : Operand 64).read s + d) 64 =
      memLoad m ((Operand.reg 3#5 : Operand 64).read s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (h.inputApart _ (by simp) _ (by simp))

theorem Pre.read_store_zero {s : RamState} (h : Pre s) (m : Ram) (c : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [128,136,144,152]) :
    memLoad (memStore m ((Operand.reg 4#5 : Operand 64).read s + c) v)
      ((Operand.reg 3#5 : Operand 64).read s) 64 =
      memLoad m ((Operand.reg 3#5 : Operand 64).read s) 64 := by
  simpa only [BitVec.add_zero] using h.read_store m c 0#64 v hc (by simp)

def bytes : List UInt8 :=
  [0x48,0x8b,0x43,0x18,0x48,0x89,0x84,0x24,0x98,0x00,0x00,0x00,0x48,0x8b,0x43,0x10,0x48,0x89,0x84,0x24,0x90,0x00,0x00,0x00,0x48,0x8b,0x03,0x48,0x8b,0x4b,0x08,0x48,0x89,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8d,0xbc,0x24,0x40,0x03,0x00,0x00,0x48,0x8d,0xb4,0x24,0x80,0x00,0x00,0x00,0x48,0x8d,0x94,0x24,0x00,0x03,0x00,0x00]

def effect (s : RamState) : Effect :=
  { rip := 0x10dd64
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), rspOf s + 768⟩,
      ⟨(Operand.reg 6 : Operand 64), rspOf s + 128⟩,
      ⟨(Operand.reg 7 : Operand 64), rspOf s + 832⟩,
      ⟨(Operand.mem (rspOf s + 128) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 136) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 144) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 152) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 24) : Operand 64).read s⟩] }

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xdd1d 71 = bytes := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 71, (0x10dd1d : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10dd1d bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10dd1d 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable15 24 (by simp)⟩
  case next =>
    intro _ _
    exact outside 4 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dd21 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 4 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 4 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0 71 (by decide)
    · exact outside 12 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dd29 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 16 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dd2d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 16 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0 71 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dd35 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 24 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 27 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dd38 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 27 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 31 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dd3c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 31 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0 71 (by decide)
    · exact outside 39 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dd44 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 39 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0 71 (by decide)
    · exact outside 47 (by decide)
  advance_then (lea_r64_effect_step 0x10dd4c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 832)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 47 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 55 (by decide)
  advance_then (lea_r64_effect_step 0x10dd54 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 55 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 63 (by decide)
  advance_then (lea_r64_effect_step 0x10dd5c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 768)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dd1d bytes 63 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 71 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, hP.read_store, hP.read_store_zero, P256.Proofs.Verifying.Core.Scalars.operand_write_reg_external,
      P256.Proofs.Verifying.Core.Scalars.operand_write_mem_external]
    all_goals try simp only [BitVec.add_zero]
    all_goals simp only [and_true]
    all_goals repeat constructor <;> first | rfl | trivial
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Core.Scalars.SecondSetup.Block
