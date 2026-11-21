import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare.CopyR.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10dad2
  readable15 : ∀ offset ∈ ([0, 8, 16, 24] : List Nat), MemReadable s ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([704, 712, 720, 728] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([704, 712, 720, 728] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 47 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10dad2 + BitVec.ofNat 64 codeOffset) len
  inputApart : ∀ offset ∈ ([704, 712, 720, 728] : List Nat), ∀ inputOffset ∈ ([0, 8, 16, 24] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 inputOffset) 8

theorem Pre.read_store {s : RamState} (h : Pre s) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [704, 712, 720, 728]) (hd : d ∈ [0, 8, 16, 24]) :
    memLoad (memStore m ((Operand.reg 4#5 : Operand 64).read s + c) v) ((Operand.reg 3#5 : Operand 64).read s + d) 64 =
      memLoad m ((Operand.reg 3#5 : Operand 64).read s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (h.inputApart _ (by simp) _ (by simp))

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x3, 0x48, 0x8b, 0x4b, 0x8, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x2, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0xc8, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x43, 0x10, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x43, 0x18, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x2, 0x0, 0x0]

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xdad2 47 = bytes := by
  decide +kernel

def effect (s : RamState) : Effect :=
  { rip := 0x10db01
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 24) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 704) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 712) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 720) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 728) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 24) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 47, (0x10dad2 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10dad2 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10dad2 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable15 0 (by simp)⟩
  case next =>
    intro _ _
    exact outside 3 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dad5 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 7 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dad9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 704)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 7 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 704 (by simp)
    · x86_norm
      exact hP.codeApart 704 (by simp) 7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 704 (by simp) 0 47 (by decide)
    · exact outside 15 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dae1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 712)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 15 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 712 (by simp)
    · x86_norm
      exact hP.codeApart 712 (by simp) 15 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 712 (by simp) 0 47 (by decide)
    · exact outside 23 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dae9 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 27 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10daed 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 720)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 27 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 720 (by simp)
    · x86_norm
      exact hP.codeApart 720 (by simp) 27 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 720 (by simp) 0 47 (by decide)
    · exact outside 35 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10daf5 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 39 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10daf9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 728)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dad2 bytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 728 (by simp)
    · x86_norm
      exact hP.codeApart 728 (by simp) 39 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 728 (by simp) 0 47 (by decide)
    · exact outside 47 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, hP.read_store]
    all_goals simp only [BitVec.add_zero]
    all_goals repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Core.Prepare.CopyR.Block
