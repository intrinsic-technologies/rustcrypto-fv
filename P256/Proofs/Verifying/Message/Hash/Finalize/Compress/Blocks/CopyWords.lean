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

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.CopyWords

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ i ∈ ([128,136,144,152,160,168,176] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([0,8,16,24,32,40,48] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24,32,40,48] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 p 90

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x30,0x48,0x8b,0x84,0x24,0xa8,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x28,0x48,0x8b,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x20,0x48,0x8b,0x84,0x24,0x98,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x18,0x48,0x8b,0x84,0x24,0x90,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x10,0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0x89,0x4c,0x24,0x8,0x48,0x89,0x4,0x24]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 90
    writes := [⟨(.reg 0 : Operand 64), (.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 0) : Operand 64), (.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), (.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), (.mem (rspOf s + 144) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), (.mem (rspOf s + 152) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), (.mem (rspOf s + 160) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), (.mem (rspOf s + 168) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), (.mem (rspOf s + 176) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 90 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 176 (by simp)⟩
  case next => exact fun _ _ => next 8 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 8) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 8 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 48 (by simp) a ha (8+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp)
    · x86_norm
      exact next 13 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 13) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 13 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 168 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 21 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 21) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 21 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 40 (by simp) a ha (21+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp)
    · x86_norm
      exact next 26 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 26) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 26 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 160 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 34 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 34) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 34 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 32 (by simp) a ha (34+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp)
    · x86_norm
      exact next 39 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 39) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 39 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 47 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 47) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 47 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 24 (by simp) a ha (47+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp)
    · x86_norm
      exact next 52 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 52) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 52 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 60 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 60) 0x48 (by simp [RexWPrefix]) 0
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
  advance_then (mov_r64_m64_effect_step (p + 65) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 65 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 73 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 73) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 73 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 81 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 81) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 81 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 8 (by simp) a ha (81+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp)
    · x86_norm
      exact next 86 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 86) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 86 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 0 (by simp) a ha (86+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp)
    · x86_norm
      exact next 90 (by decide)
  advance_finish [effect, BitVec.add_zero]

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.CopyWords
