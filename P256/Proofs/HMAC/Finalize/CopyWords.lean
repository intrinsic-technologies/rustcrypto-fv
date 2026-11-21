import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

open P256.Proofs.Program

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.CopyWords

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ i ∈ ([72,80,88,96,104,112,120] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([8,16,24,32,40,48,56] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([8,16,24,32,40,48,56] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 p 70

def bytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x78,0x48,0x89,0x44,0x24,0x38,0x48,0x8b,0x44,0x24,0x70,0x48,0x89,0x44,0x24,0x30,0x48,0x8b,0x44,0x24,0x68,0x48,0x89,0x44,0x24,0x28,0x48,0x8b,0x44,0x24,0x60,0x48,0x89,0x44,0x24,0x20,0x48,0x8b,0x44,0x24,0x58,0x48,0x89,0x44,0x24,0x18,0x48,0x8b,0x44,0x24,0x48,0x48,0x8b,0x4c,0x24,0x50,0x48,0x89,0x4c,0x24,0x10,0x48,0x89,0x44,0x24,0x8]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 70
    writes := [⟨(.reg 0 : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), (.mem (rspOf s + 104) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), (.mem (rspOf s + 112) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), (.mem (rspOf s + 120) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 70 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 120 (by simp)⟩
  case next => exact fun _ _ => next 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 56 (by simp) a ha (5+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp)
    · x86_norm
      exact next 10 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 10) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 10 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 112 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 15 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 15) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 15 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 48 (by simp) a ha (15+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp)
    · x86_norm
      exact next 20 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 20) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 20 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 104 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 25 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 25) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 40 (by simp) a ha (25+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp)
    · x86_norm
      exact next 30 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 30) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 30 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 35 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 35) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 35 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 32 (by simp) a ha (35+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp)
    · x86_norm
      exact next 40 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 40) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 40 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 88 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 45 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 45) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 45 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 24 (by simp) a ha (45+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp)
    · x86_norm
      exact next 50 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 50) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 50 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 72 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 55 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 55) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 55 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat] using hP.readable 80 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 60 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 60) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 60 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 16 (by simp) a ha (60+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp)
    · x86_norm
      exact next 65 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 65) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 65 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 8 (by simp) a ha (65+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp)
    · x86_norm
      exact next 70 (by decide)
  advance_finish [effect]

end P256.Proofs.HMAC.Finalize.CopyWords
