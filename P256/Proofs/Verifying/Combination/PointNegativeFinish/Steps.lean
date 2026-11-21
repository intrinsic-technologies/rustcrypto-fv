import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Verifying.Combination.PointMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.NegativeFinish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10f241
  target : (Operand.reg (14#5) : Operand 64).read s = (Operand.reg (4#5) : Operand 64).read s + 296
  readable : ∀ offset : Nat, offset + 8 ≤ 408 →
    MemReadable s ((Operand.reg (4#5) : Operand 64).read s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset : Nat, offset + 8 ≤ 360 → offset % 8 = 0 →
    MemWritable s ((Operand.reg (4#5) : Operand 64).read s + BitVec.ofNat 64 offset) 8
  apart : ∀ offset pc len : Nat, offset + 8 ≤ 360 → pc + len ≤ 118431 →
    RangeApart ((Operand.reg (4#5) : Operand 64).read s + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x8c, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x41, 0x18, 0x49, 0x89, 0x46, 0x38, 0x48, 0x8b, 0x41, 0x10, 0x49, 0x89, 0x46, 0x30, 0x48, 0x8b, 0x1, 0x48, 0x8b, 0x49, 0x8, 0x49, 0x89, 0x4e, 0x28, 0x49, 0x89, 0x46, 0x20]

def effect (s : RamState) : Effect :=
  let sp := (Operand.reg (4#5) : Operand 64).read s
  let word (offset : BitVec 64) := memLoad s.external (sp + offset) 64
  { rip := 0x10f2a8
    writes := [⟨(Operand.reg 0 : Operand 64), word 232⟩,
      ⟨(Operand.reg 1 : Operand 64), word 240⟩,
      ⟨(Operand.mem (sp + 288) : Operand 64), word 192⟩,
      ⟨(Operand.mem (sp + 280) : Operand 64), word 184⟩,
      ⟨(Operand.mem (sp + 272) : Operand 64), word 176⟩,
      ⟨(Operand.mem (sp + 264) : Operand 64), word 168⟩,
      ⟨(Operand.mem (sp + 352) : Operand 64), word 256⟩,
      ⟨(Operand.mem (sp + 344) : Operand 64), word 248⟩,
      ⟨(Operand.mem (sp + 336) : Operand 64), word 240⟩,
      ⟨(Operand.mem (sp + 328) : Operand 64), word 232⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10f241 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10f241 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 0 8
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    exact hP.readable 192 (by decide)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0xf249 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10f249 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 288)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf251 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 288 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 288 0xf249 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 288 0xf241 103 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f251 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf259 (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 184 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f259 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 280)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf261 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 280 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 280 0xf259 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 280 0xf241 103 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f261 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf269 (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 168 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f269 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf271 (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 176 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f271 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 272)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf279 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 272 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 272 0xf271 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 272 0xf241 103 (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f279 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 264)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf281 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 264 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 264 0xf279 8 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 264 0xf241 103 (by decide) (by decide)
  advance_then (lea_r64_effect_step 0x10f281 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 64 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf289 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x10f289 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 24)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 72 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf28d (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 256 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f28d 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 56)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 76 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf291 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 352 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 352 0xf28d 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 352 0xf241 103 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f291 0x48 (by simp [RexWPrefix]) 0
    (.base 1 (.d8 16)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 80 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf295 (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 248 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f295 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 48)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 84 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf299 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 344 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 344 0xf295 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 344 0xf241 103 (by decide) (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f299 0x48 (by simp [RexWPrefix]) 0
    (.base 1 .none) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 88 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf29c (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 232 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10f29c 0x48 (by simp [RexWPrefix]) 1
    (.base 1 (.d8 8)) (by decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 91 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xf2a0 (by decide))⟩
    x86_norm
    try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    exact hP.readable 240 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f2a0 0x49 (by simp [RexWPrefix]) 1
    (.base 14 (.d8 40)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 95 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf2a4 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 336 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 336 0xf2a0 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 336 0xf241 103 (by decide) (by decide)
  advance_then (mov_m64_r64_effect_step 0x10f2a4 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 32)) (by constructor <;> decide +kernel) rfl rfl)
  all_goals try exact codeRange_slice_subset 0x10f241 bytes 99 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_,
      boundary_ne_program outside (inProgram_of_textOffset 0xf2a8 (by decide))⟩
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.writable 328 (by decide) (by decide)
    · x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 328 0xf2a4 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      try (rw [hP.target]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact hP.apart 328 0xf241 103 (by decide) (by decide)
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
    all_goals try simp only [hP.target, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try x86_norm
  · x86_norm [effect]
    all_goals try simp only [hP.target, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try x86_norm
  · intro i; cases i <;> x86_norm [effect, hP.target]
  · x86_norm [effect]
    all_goals try simp only [hP.target, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try x86_norm

end P256.Proofs.Verifying.Combination.Loop.Multi.NegativeFinish
