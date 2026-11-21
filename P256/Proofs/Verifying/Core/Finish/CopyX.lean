import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.CopyX

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable4 : ∀ offset ∈ ([896, 904, 912, 920] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([576, 584, 592, 600] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([576, 584, 592, 600] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 64 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (p + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x98,0x3,0x0,0x0,0x48,0x89,0x84,0x24,0x58,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0x90,0x3,0x0,0x0,0x48,0x89,0x84,0x24,0x50,0x2,0x0,0x0,0x48,0x8b,0x84,0x24,0x80,0x3,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x3,0x0,0x0,0x48,0x89,0x8c,0x24,0x48,0x2,0x0,0x0,0x48,0x89,0x84,0x24,0x40,0x2,0x0,0x0]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 64
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (rspOf s + 896) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem (rspOf s + 904) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 576) : Operand 64), (Operand.mem (rspOf s + 896) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 584) : Operand 64), (Operand.mem (rspOf s + 904) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 592) : Operand 64), (Operand.mem (rspOf s + 912) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 600) : Operand 64), (Operand.mem (rspOf s + 920) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 64, p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 920)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable4 920 (by simp)⟩
  case next =>
    intro _ _
    exact outside 8 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 8) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 600)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 600 (by simp)
    · x86_norm
      exact hP.codeApart 600 (by simp) 8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 600 (by simp) 0 64 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 16 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 16) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 912)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 912 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 24 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 24) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 592)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 592 (by simp)
    · x86_norm
      exact hP.codeApart 592 (by simp) 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 592 (by simp) 0 64 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 32 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 32) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 896)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 896 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 40 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 40) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 904)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 904 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 48 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 48) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 584)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 584 (by simp)
    · x86_norm
      exact hP.codeApart 584 (by simp) 48 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 584 (by simp) 0 64 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 56) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 576)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 576 (by simp)
    · x86_norm
      exact hP.codeApart 576 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 576 (by simp) 0 64 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 64 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, BitVec.add_assoc]
  · x86_norm [effect]
    all_goals try simp only [BitVec.add_zero]
    all_goals repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [effect, BitVec.add_assoc]
  · x86_norm [effect, BitVec.add_assoc]

end P256.Proofs.Verifying.Core.Finish.CopyX
