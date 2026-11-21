import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
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

namespace Sha2.Proofs.Wrapper.Hash.Padding.CopyWords

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)

structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ i ∈ ([0,8,16,24,32,40,48] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([104,112,120,128,136,144,152] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([104,112,120,128,136,144,152] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 p 81

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x4, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68]

def effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 81
    writes := [⟨(.reg 0 : Operand 64), (.mem (rspOf s) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), (.mem (rspOf s + 0) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), (.mem (rspOf s + 8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 120) : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 128) : Operand 64), (.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 136) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 144) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 152) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 81 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p bytes) (Effect.post (effect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 48 (by simp)⟩
  case next => exact fun _ _ => next 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 5) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 152 (by simp) a ha (5+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp)
    · x86_norm
      exact next 13 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 13) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 18 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 18) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 18 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 144 (by simp) a ha (18+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp)
    · x86_norm
      exact next 26 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 26) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 26 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 31 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 31) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 31 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 136 (by simp) a ha (31+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp)
    · x86_norm
      exact next 39 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 39) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 39 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 44 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 44) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 44 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 128 (by simp) a ha (44+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp)
    · x86_norm
      exact next 52 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 52) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 52 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 57 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 57) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 57 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 120 (by simp) a ha (57+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 (by simp)
    · x86_norm
      exact next 62 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 62) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 62 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 66 (by decide)
  advance_then (mov_r64_m64_effect_step (p + 66) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 66 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact next 71 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 71) 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 71 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 112 (by simp) a ha (71+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 (by simp)
    · x86_norm
      exact next 76 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 76) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p bytes 76 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 104 (by simp) a ha (76+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 (by simp)
    · x86_norm
      exact next 81 (by decide)
  advance_finish [effect, BitVec.add_zero]

end Sha2.Proofs.Wrapper.Hash.Padding.CopyWords
