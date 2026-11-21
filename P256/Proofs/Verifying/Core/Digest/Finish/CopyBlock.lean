import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Finish.CopyBlock

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable4 : ∀ offset ∈ ([0, 8, 16, 24] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 51 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (p + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x4, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x8c, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 51
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (rspOf s + 0) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 128) : Operand 64), (Operand.mem (rspOf s + 0) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 136) : Operand 64), (Operand.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 144) : Operand 64), (Operand.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 152) : Operand 64), (Operand.mem (rspOf s + 24) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 51, p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable4 24 (by simp)⟩
  case next =>
    intro _ _
    exact outside 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 152 (by simp) 0 51 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 13 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 13) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 18 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 18) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 18 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 144 (by simp) 0 51 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 26 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 26) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 30 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 30) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 35 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 35) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 35 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 136 (by simp) 0 51 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 43 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 43) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 43 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      have h := hP.codeApart 128 (by simp) 0 51 (by decide)
      x86_norm at h
      simpa only [BitVec.add_zero] using h
    · x86_norm
      simpa only [BitVec.add_assoc] using outside 51 (by decide)
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

end P256.Proofs.Verifying.Core.Digest.Finish.CopyBlock
