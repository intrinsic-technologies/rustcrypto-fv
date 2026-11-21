import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Wrapper.Memory
import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import Hkdf.Proofs.Common.Instructions.RepMovsq.Memory
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.SHA256

structure CompressedPads [Bindings] (initial s : RamState) (salt : Option ByteArray) : Prop
    extends Standard.Preserved initial s where
  rip : s.RIP = 0x10155f
  innerHash : HashStateAt s (frameBase initial + 56)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
      (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36))
  innerBlocks : loadBytes s.external (frameBase initial + 88) 8 = .ok 1
  outerHash : HashStateAt s (frameBase initial + 16)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
      (HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x5c))
  outerBlocks : loadBytes s.external (frameBase initial + 48) 8 = .ok 1


open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

private structure LayoutPre (s : RamState) : Prop where
  rip : s.RIP = 0x10155f
  readable : ∀ i ∈ ([16,24,32,40,48,56,64,72,80,88] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([328,336,344,352,360,368,376,384,392,400] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  lengthWritable : MemWritable s (rspOf s + 183) 1
  codeApart : ∀ i ∈ ([328,336,344,352,360,368,376,384,392,400] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 0x10155f 159
  lengthCodeApart : RangeApart (rspOf s + 183) 1 0x10155f 159

private def layoutBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x30,0x48,0x89,0x84,0x24,0x90,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x28,0x48,0x89,0x84,0x24,0x88,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x20,0x48,0x89,0x84,0x24,0x80,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x10,0x48,0x8b,0x4c,0x24,0x18,0x48,0x89,0x8c,0x24,0x78,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x70,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x38,0x48,0x8b,0x4c,0x24,0x40,0x48,0x89,0x84,0x24,0x48,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x50,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x48,0x48,0x89,0x84,0x24,0x58,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x50,0x48,0x89,0x84,0x24,0x60,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x58,0x48,0x89,0x84,0x24,0x68,0x1,0x0,0x0,0xc6,0x84,0x24,0xb7,0x0,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb8,0x0,0x0,0x0,0x48,0x8d,0xb4,0x24,0x48,0x1,0x0,0x0,0xb9,0xa,0x0,0x0,0x0]

private def layoutEffect (s : RamState) : Effect :=
  { rip := 0x1015fe
    writes := [⟨(.reg 0 : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), 10⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 184⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 328⟩,
      ⟨(.mem (rspOf s + 183) : Operand 8), 0⟩,
      ⟨(.mem (rspOf s + 400) : Operand 64), (.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 392) : Operand 64), (.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 384) : Operand 64), (.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 368) : Operand 64), (.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 376) : Operand 64), (.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 328) : Operand 64), (.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 336) : Operand 64), (.mem (rspOf s + 64) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 344) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 352) : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 360) : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩] }

set_option maxHeartbeats 1800000 in
private theorem layout_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LayoutPre (codeRange 0x10155f layoutBytes)
      (Effect.post layoutEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10155f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 48 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1564 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101564 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 400)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 400 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 400 (by simp) a ha (5+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 400 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x156c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10156c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 13 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1571 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101571 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 18 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 392 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 392 (by simp) a ha (18+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 392 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1579 (by decide))
  advance_then (mov_r64_m64_effect_step 0x101579 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 26 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x157e (by decide))
  advance_then (mov_m64_r64_effect_step 0x10157e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 384)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 31 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 384 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 384 (by simp) a ha (31+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 384 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1586 (by decide))
  advance_then (mov_r64_m64_effect_step 0x101586 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 39 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x158b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10158b 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 44 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1590 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101590 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 376)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 49 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 376 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 376 (by simp) a ha (49+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 376 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1598 (by decide))
  advance_then (mov_m64_r64_effect_step 0x101598 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 368)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 57 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 368 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 368 (by simp) a ha (57+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 368 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15a0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1015a0 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 65 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15a5 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1015a5 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 70 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 64 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15aa (by decide))
  advance_then (mov_m64_r64_effect_step 0x1015aa 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 75 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 328 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 328 (by simp) a ha (75+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 328 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15b2 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1015b2 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 83 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 336 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 336 (by simp) a ha (83+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 336 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15ba (by decide))
  advance_then (mov_r64_m64_effect_step 0x1015ba 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 91 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15bf (by decide))
  advance_then (mov_m64_r64_effect_step 0x1015bf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 96 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 344 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 344 (by simp) a ha (96+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 344 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15c7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1015c7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 104 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 80 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15cc (by decide))
  advance_then (mov_m64_r64_effect_step 0x1015cc 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 109 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 352 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 352 (by simp) a ha (109+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 352 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15d4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1015d4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 117 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15d9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1015d9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 122 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 360 (by simp)
    · x86_norm
      intro a ha b hb
      have separate := hP.codeApart 360 (by simp) a ha (122+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 360 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15e1 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x1015e1 (.sib 4 none 0 (.d32 183)) (by decide) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 130 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.lengthWritable
    · x86_norm
      intro a ha b hb
      have separate := hP.lengthCodeApart a ha (130+b) (by omega)
      simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add,
        ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.lengthCodeApart
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15e9 (by decide))
  advance_then (lea_r64_effect_step 0x1015e9 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 138 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15f1 (by decide))
  advance_then (lea_r64_effect_step 0x1015f1 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 146 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15f9 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1015f9 0xb9 (by decide) 10)
  try (case sub => exact codeRange_slice_subset 0x10155f layoutBytes 154 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x15fe (by decide))
  advance_finish [layoutEffect, BitVec.add_zero]


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem assemble [bindings : Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Standard.Context initial salt inputs)
    (pads : CompressedPads initial s salt) : ∃ t, Standard.Initialized initial t salt := by
  have bounds := Standard.stack_bounds ctx
  have address (offset : Nat) (h : offset ≤ 520) :
      frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
    have eq := Standard.stack_address pads.rsp h
    change s.regValue .rsp + BitVec.ofNat 64 offset = _ at eq
    rw [pads.rsp] at eq
    exact eq
  have addressNat (offset : Nat) (h : offset ≤ 520) :
      (frameBase initial + BitVec.ofNat 64 offset).toNat =
        (stackPtr initial).toNat - (520 - offset) := by
    rw [address offset h]
    exact Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (by change 520-offset ≤ 1792; omega)
  have rspS : rspOf s = frameBase initial := pads.rsp
  have readable (offset len : Nat) (ho : offset ≤ 520) (hl : len ≤ 528 - offset) :
      MemReadable s (frameBase initial + BitVec.ofNat 64 offset) len := by
    rw [address offset ho]
    exact Standard.stack_readable ctx pads.toState (by omega) (by omega)
  have writable (offset : Nat) (ho : offset ≤ 520) (ha : offset % 8 = 0) :
      MemWritable s (frameBase initial + BitVec.ofNat 64 offset) 8 := by
    rw [address offset ho]
    apply Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
      (Standard.initial_stack_writable8 ctx (by omega) (by omega)) pads.allocated
  have lengthWritable : MemWritable s (frameBase initial + BitVec.ofNat 64 183) 1 := by
    rw [address 183 (by decide)]
    apply Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
      (Standard.initial_stack_writable ctx (by decide) (by decide) (by decide)
        (by have := Nat.mod_lt (stackPtr initial - BitVec.ofNat 64 (520-183)).toNat
              (show 0 < 4096 by decide); omega)) pads.allocated
  have codeApart (offset len : Nat) (ho : offset ≤ 520) (hl : len ≤ 520-offset) :
      RangeApart (frameBase initial + BitVec.ofNat 64 offset) len 0x10155f 159 := by
    rw [address offset ho]
    exact Standard.stack_codeApart ctx (codeOffset := 0x155f)
      (by omega) hl (by decide)
  have pre : LayoutPre s := by
    refine ⟨pads.rip, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact readable _ _ (by decide) (by decide)
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact writable _ (by decide) (by decide)
    · simpa only [rspS, BitVec.ofNat_eq_ofNat] using lengthWritable
    · intro i hi
      rw [rspS]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact codeApart _ _ (by decide) (by decide)
    · simpa only [rspS, BitVec.ofNat_eq_ofNat] using codeApart 183 1 (by decide) (by decide)
  have outside := (Standard.returnBoundary_valid ctx).2.2
  obtain ⟨fuel, u, runU, readyU, _, effectU⟩ := layout_run (returnBoundary initial)
    outside s (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep pads.machine)
    (programText_slice (programLoaded_codeIn pads.loaded) 0x155f layoutBytes
      (by decide) (by decide +kernel)) pre
  let written : MemoryRegion := ⟨(frameBase initial + BitVec.ofNat 64 183).toNat, 225⟩
  have contains {offset len : Nat} (low : 183 ≤ offset) (high : offset+len ≤ 408)
      {a : BitVec 64} (ha : (Component.mem
        (frameBase initial + BitVec.ofNat 64 offset) len).Covers a) :
      written.Contains a.toNat := by
    obtain ⟨j, hj, rfl⟩ := ha
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, addressNat (offset+j) (by omega)]
    change (frameBase initial + BitVec.ofNat 64 183).toNat ≤ _ ∧
      _ < (frameBase initial + BitVec.ofNat 64 183).toNat + 225
    rw [addressNat 183 (by decide)]
    constructor <;> omega
  have footprintU : WritesWithin (layoutEffect s).components #v[written] := by
    intro c hc a ha
    simp only [layoutEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [rspS] at ha
    all_goals exact ⟨written, by simp, contains (by decide) (by decide) ha⟩
  have inStack {a : Nat} (ha : written.Contains a) :
      (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a := by
    change (frameBase initial + BitVec.ofNat 64 183).toNat ≤ a ∧
      a < (frameBase initial + BitVec.ofNat 64 183).toNat + 225 at ha
    rw [addressNat 183 (by decide)] at ha
    change (Stack.region initial 1792).Contains a
    unfold MemoryRegion.Contains
    rw [Hkdf.Proofs.Common.Machine.stack_region_end]
    change (stackPtr initial).toNat - 1792 ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have avoids : ∀ region ∈ #v[Stack.region initial hkdfSha256Extract.minStackBytes],
      region.Avoids InProgram := by
    intro region hr a ha hin
    exact (ctx.call.stackSeparation.2 region (by simpa using hr)).2 a ha (.inl hin)
  have runningU := pads.toRunning.of_agrees runU readyU effectU.agrees
    (by intro c hc a ha
        obtain ⟨region, hr, hin⟩ := footprintU c hc a ha
        have eq : region = written := by simpa using hr
        subst region
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp, inStack hin⟩)
    avoids (by simp [layoutEffect, Effect.components, Write.component, Operand.component])
  have frameU := effectU.agrees.memoryWriteFrame footprintU
  have stores := effectU.writes
  simp only [layoutEffect, Write.AllHold, Operand.read, rspS] at stores
  have outputU : rdi.read u = frameBase initial + BitVec.ofNat 64 184 := stores.2.2.1
  have inputU : rsi.read u = frameBase initial + BitVec.ofNat 64 328 := stores.2.2.2.1
  have countU : (rcx.read u).toNat = 10 := by
    have count : rcx.read u = 10 := stores.2.1
    rw [count]; rfl
  have uReadable (offset len : Nat) (ho : offset ≤ 520) (hl : len ≤ 528-offset) :
      MemReadable u (frameBase initial + BitVec.ofNat 64 offset) len := by
    rw [address offset ho]
    exact Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
      (Standard.initial_stack_readable ctx (by omega) (by omega)) runningU.allocated
  have targetWrite : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable u
      (frameBase initial + BitVec.ofNat 64 184) 80 := by
    refine ⟨uReadable 184 80 (by decide) (by decide), ?_⟩
    apply tables_of_not_reserved (by decide)
      (uReadable 184 80 (by decide) (by decide)).low
    intro i hi reserved
    apply (ctx.call.stackSeparation.2 (Stack.region initial hkdfSha256Extract.minStackBytes)
      (by simp)).2 _ ?_ (.inr reserved)
    apply inStack
    apply contains (offset := 184) (len := 80) (by decide) (by decide)
    exact ⟨i, hi, rfl⟩
  have repPre : Hkdf.Proofs.Common.Instructions.RepMovsq.RepMovsqPre 0x1015fe u := by
    apply Hkdf.Proofs.Common.Instructions.RepMovsq.pre_of_memory effectU.rip
      runningU.directionFlag.df countU
    · rw [inputU]
      exact uReadable 328 80 (by decide) (by decide)
    · rw [outputU]
      exact targetWrite
    · rw [inputU, outputU, addressNat 328 (by decide), addressNat 184 (by decide)]
      right
      omega
    · rw [outputU, address 184 (by decide)]
      exact Standard.stack_codeApart ctx (codeOffset := 0x15fe)
        (by decide) (by decide) (by decide)
  have rep := Hkdf.Proofs.Common.Instructions.RepMovsq.rep_movsq_execution
    ctx.environment.stringStride readyU
    (programText_slice (programLoaded_codeIn runningU.loaded) 0x15fe
      [0xf3,0x48,0xa5] (by decide) (by decide +kernel)) repPre countU
    (boundary_ne_program outside (inProgram_of_textOffset 0x15fe (by decide)))
    (boundary_ne_program outside (inProgram_of_textOffset 0x1601 (by decide)))
  change Advances (returnBoundary initial) 10 u (nextStates 10 u) ∧
    ReadyToStep (nextStates 10 u) ∧
    (repMovsqEffect 0x1015fe u).Holds u (nextStates 10 u) ∧
      (∀ i < 80, (nextStates 10 u).external[rdi.read u + BitVec.ofNat 64 i]? =
        u.external[rsi.read u + BitVec.ofNat 64 i]?) at rep
  generalize endpoint : nextStates 10 u = t at rep
  obtain ⟨runT, readyT, effectT, copied⟩ := rep
  have footprintT : WritesWithin (repMovsqEffect 0x1015fe u).components #v[written] := by
    intro c hc a ha
    simp only [repMovsqEffect_components, countU, outputU, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨written, by simp, contains (offset := 184) (len := 80)
      (by decide) (by decide) ha⟩
  have runningT := runningU.of_agrees runT readyT effectT.agrees
    (by intro c hc a ha
        obtain ⟨region, hr, hin⟩ := footprintT c hc a ha
        have eq : region = written := by simpa using hr
        subst region
        exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp, inStack hin⟩)
    avoids (by simp [repMovsqEffect_components])
  have finalFrame := memoryWriteFrame_trans frameU
    (effectT.agrees.memoryWriteFrame footprintT)
  have preserved : Standard.Preserved initial t := by
    apply pads.toPreserved.of_observations runningT
    · apply CallFrame.frame_agrees_of_disjoint finalFrame
      · have nat48 : (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 := by
          simpa only [BitVec.ofNat_eq_ofNat] using
            Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 48) (by decide)
        rw [nat48]
        omega
      · intro region hr
        have eq : region = written := by simpa using hr
        subst region
        intro a ha hb
        change (stackPtr initial - 48).toNat ≤ a ∧
          a < (stackPtr initial - 48).toNat + 56 at ha
        change (frameBase initial + BitVec.ofNat 64 183).toNat ≤ a ∧
          a < (frameBase initial + BitVec.ofNat 64 183).toNat + 225 at hb
        rw [addressNat 183 (by decide)] at hb
        have nat48 : (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 := by
          simpa only [BitVec.ofNat_eq_ofNat] using
            Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 48) (by decide)
        rw [nat48] at ha
        omega
    · intro offset ho
      apply CallFrame.frame_agrees_of_disjoint finalFrame
      · rw [addressNat offset (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          omega)]
        omega
      · intro region hr
        have eq : region = written := by simpa using hr
        subst region
        have off : offset ≤ 112 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          omega
        intro a ha hb
        change (frameBase initial + BitVec.ofNat 64 offset).toNat ≤ a ∧
          a < (frameBase initial + BitVec.ofNat 64 offset).toNat + 8 at ha
        change (frameBase initial + BitVec.ofNat 64 183).toNat ≤ a ∧
          a < (frameBase initial + BitVec.ofNat 64 183).toNat + 225 at hb
        rw [addressNat offset (by omega)] at ha
        rw [addressNat 183 (by decide)] at hb
        omega
    · exact (effectT.agrees.read (n := 64) (r := 4) (by
        simp [repMovsqEffect_components])).trans
        ((effectU.agrees.read (n := 64) (r := 4) (by
          simp [layoutEffect, Effect.components, Write.component, Operand.component])).trans pads.rsp)
  have words : ∀ j < 10,
      memLoad u.external (frameBase initial + BitVec.ofNat 64 328 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64
          (if j < 5 then 56+8*j else 16+8*(j-5))) 64 := by
    intro j hj
    rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨
      j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero] using stores.2.2.2.2.2.1
  have moved : ∀ i < 80,
      t.external[frameBase initial + BitVec.ofNat 64 184 + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64
          (if i < 40 then 56+i else 16+(i-40))]? := by
    intro i hi
    have dst := copied i (by omega)
    rw [outputU, inputU] at dst
    have ub := Bytes.of_memLoad (n := 64)
      (m := u.external) (a := frameBase initial + BitVec.ofNat 64 328 + BitVec.ofNat 64 (8*(i/8)))
      (by intro j hj
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact (uReadable 328 80 (by decide) (by decide)).mem _ (by omega))
    have sb := Bytes.of_memLoad (n := 64)
      (m := s.external) (a := frameBase initial + BitVec.ofNat 64
        (if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5)))
      (by intro j hj
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          have range : (if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5)) + j < 96 := by
            split <;> omega
          have low : 16 ≤ (if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5)) + j := by
            split <;> omega
          have h := (readable 16 80 (by decide) (by decide)).mem
            ((if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5))+j-16) (by omega)
          simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' low] using h)
    rw [words (i/8) (by omega)] at ub
    have byte := (ub (i%8) (by omega)).trans (sb (i%8) (by omega)).symm
    have leftAddr : frameBase initial + BitVec.ofNat 64 328 + BitVec.ofNat 64 (8*(i/8)) +
        BitVec.ofNat 64 (i%8) = frameBase initial + BitVec.ofNat 64 328 + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc (frameBase initial + BitVec.ofNat 64 328), ← BitVec.ofNat_add,
        show 8*(i/8)+i%8=i by omega]
    have rightAddr : frameBase initial + BitVec.ofNat 64
        (if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5)) + BitVec.ofNat 64 (i%8) =
        frameBase initial + BitVec.ofNat 64 (if i < 40 then 56+i else 16+(i-40)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have arithmetic : (if i/8 < 5 then 56+8*(i/8) else 16+8*(i/8-5)) + i%8 =
          (if i < 40 then 56+i else 16+(i-40)) := by split <;> split <;> omega
      rw [arithmetic]
    rw [leftAddr, rightAddr] at byte
    exact dst.trans byte
  have addOffsets (base : BitVec 64) (a b : Nat) :
      base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a+b) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have innerHash := Hkdf.Proofs.Wrapper.hashState_of_bytes (t := t) pads.innerHash
    (b := hmacBase initial + 64) (by
      intro i hi
      have h := moved i (by omega)
      simp only [show i < 40 by omega, ite_true] at h
      simpa only [hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat] using h)
  have outerHash := Hkdf.Proofs.Wrapper.hashState_of_bytes (t := t) pads.outerHash
    (b := hmacBase initial + 104) (by
      intro i hi
      have h := moved (40+i) (by omega)
      simp only [show ¬40+i<40 by omega, ite_false, Nat.add_sub_cancel_left] at h
      change t.external[(frameBase initial + BitVec.ofNat 64 120) + BitVec.ofNat 64 104 +
          BitVec.ofNat 64 i]? = s.external[(frameBase initial + BitVec.ofNat 64 16) +
          BitVec.ofNat 64 i]?
      simpa only [addOffsets, ← Nat.add_assoc, Nat.reduceAdd] using h)
  have innerBlocks : loadBytes t.external (hmacBase initial + 96) 8 = .ok 1 := by
    apply Bytes.loadBytes64
    intro i hi
    have h := moved (32+i) (by omega)
    simp only [show 32+i<40 by omega, ite_true] at h
    have old := Hkdf.Proofs.Common.Memory.bytes_of_loadBytes64 pads.innerBlocks i hi
    apply Eq.trans _ old
    change t.external[(frameBase initial + BitVec.ofNat 64 120) + BitVec.ofNat 64 96 +
        BitVec.ofNat 64 i]? = s.external[(frameBase initial + BitVec.ofNat 64 88) +
        BitVec.ofNat 64 i]?
    simpa only [addOffsets, ← Nat.add_assoc, Nat.reduceAdd] using h
  have outerBlocks : loadBytes t.external (hmacBase initial + 136) 8 = .ok 1 := by
    apply Bytes.loadBytes64
    intro i hi
    have h := moved (72+i) (by omega)
    simp only [show ¬72+i<40 by omega, ite_false] at h
    have arithmetic : 16+(72+i-40) = 48+i := by omega
    rw [arithmetic] at h
    have old := Hkdf.Proofs.Common.Memory.bytes_of_loadBytes64 pads.outerBlocks i hi
    apply Eq.trans _ old
    change t.external[(frameBase initial + BitVec.ofNat 64 120) + BitVec.ofNat 64 136 +
        BitVec.ofNat 64 i]? = s.external[(frameBase initial + BitVec.ofNat 64 48) +
        BitVec.ofNat 64 i]?
    simpa only [addOffsets, ← Nat.add_assoc, Nat.reduceAdd] using h
  have lengthU : u.external[frameBase initial + BitVec.ofNat 64 183]? = some 0 := by
    have bytes := Bytes.of_memLoad (n := 8) (uReadable 183 1 (by decide) (by decide)).mem
    have word : memLoad u.external (frameBase initial + BitVec.ofNat 64 183) 8 = 0 :=
      stores.2.2.2.2.1
    rw [word] at bytes
    simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl]
      using bytes 0 (by decide)
  have lengthT : t.external[hmacBase initial + 63]? = some 0 := by
    have same := effectT.agrees.byte (x := frameBase initial + BitVec.ofNat 64 183) (by
      intro c hc ha
      simp only [repMovsqEffect_components, countU, outputU, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨j, hj, eq⟩ := ha
      exact OffsetsApart.ne (c₁ := 183) (len₁ := 1) (c₂ := 184) (len₂ := 80)
        (by unfold OffsetsApart; decide +kernel) (frameBase initial)
        (i := 0) (by decide) hj (by decide) (by simpa using eq))
    simpa only [hmacBase, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using same.trans lengthU
  have hmac : HmacAt t (hmacBase initial) (saltKey salt) ByteArray.empty := by
    have emptyAppend : HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 ++
        ByteArray.empty = HMAC.xorPad (HMAC.keyBlock (saltKey salt)) 0x36 := by simp
    refine ⟨?_, outerHash, outerBlocks⟩
    rw [emptyAppend]
    apply (StreamAt.single_block_iff (HMAC.xorPad_keyBlock_size (saltKey salt) 0x36)).mpr
    refine ⟨?_, lengthT, innerBlocks⟩
    simpa only [compressBlocks_single _ _ (HMAC.xorPad_keyBlock_size (saltKey salt) 0x36)]
      using innerHash
  exact ⟨t, ⟨⟨preserved, hmac⟩, effectT.rip⟩⟩

end Hkdf.Proofs.Standard.Initialization
