import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare.CopyS.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10db7f
  readable15 : ∀ offset ∈ ([32, 40, 48, 56] : List Nat), MemReadable s ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([736, 744, 752, 760] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([736, 744, 752, 760] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 51 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10db7f + BitVec.ofNat 64 codeOffset) len
  inputApart : ∀ offset ∈ ([736, 744, 752, 760] : List Nat), ∀ inputOffset ∈ ([32, 40, 48, 56] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      ((Operand.reg 3#5 : Operand 64).read s + BitVec.ofNat 64 inputOffset) 8

theorem Pre.read_store {s : RamState} (h : Pre s) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [736, 744, 752, 760]) (hd : d ∈ [32, 40, 48, 56]) :
    memLoad (memStore m ((Operand.reg 4#5 : Operand 64).read s + c) v) ((Operand.reg 3#5 : Operand 64).read s + d) 64 =
      memLoad m ((Operand.reg 3#5 : Operand 64).read s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (h.inputApart _ (by simp) _ (by simp))

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x43, 0x20, 0x48, 0x8b, 0x8, 0x48, 0x8b, 0x50, 0x8, 0x48, 0x89, 0x8c, 0x24, 0xe0, 0x2, 0x0, 0x0, 0x48, 0x89, 0x94, 0x24, 0xe8, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x48, 0x10, 0x48, 0x89, 0x8c, 0x24, 0xf0, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x40, 0x18, 0x48, 0x89, 0x84, 0x24, 0xf8, 0x2, 0x0, 0x0]

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xdb7f 51 = bytes := by
  decide +kernel

def effect (s : RamState) : Effect :=
  { rip := 0x10dbb2
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 56) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 48) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 40) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 736) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 32) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 744) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 40) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 752) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 48) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 760) : Operand 64), (Operand.mem ((Operand.reg 3#5 : Operand 64).read s + 56) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 51, (0x10db7f : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10db7f bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10db7f 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact outside 4 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db83 0x48 (by simp [RexWPrefix]) 1 (.base 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 7 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db86 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 11 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db8a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 736)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 736 (by simp)
    · x86_norm
      exact hP.codeApart 736 (by simp) 11 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 736 (by simp) 0 51 (by decide)
    · exact outside 19 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db92 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 744)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 19 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 744 (by simp)
    · x86_norm
      exact hP.codeApart 744 (by simp) 19 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 744 (by simp) 0 51 (by decide)
    · exact outside 27 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10db9a 0x48 (by simp [RexWPrefix]) 1 (.base 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 27 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 31 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10db9e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 752)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 752 (by simp)
    · x86_norm
      exact hP.codeApart 752 (by simp) 31 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 752 (by simp) 0 51 (by decide)
    · exact outside 39 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dba6 0x48 (by simp [RexWPrefix]) 0 (.base 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 39 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable15 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 43 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dbaa 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 760)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10db7f bytes 43 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 760 (by simp)
    · x86_norm
      exact hP.codeApart 760 (by simp) 43 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 760 (by simp) 0 51 (by decide)
    · exact outside 51 (by decide)
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

end P256.Proofs.Verifying.Core.Prepare.CopyS.Block
