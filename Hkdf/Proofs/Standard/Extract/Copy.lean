import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Key.Tail.Copy
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Extract.Copy

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.Field
open Hkdf.Proofs.Key.Tail.Copy (external_write_reg external_write_mem)

abbrev Writable := Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable

def outputPtr (s : RamState) : BitVec 64 := memLoad s.external (rspOf s + 96) 64

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10174c
  readable : ∀ i ∈ ([96,120,128,136,144] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  stackWritable : ∀ i ∈ ([16,24,32,40] : List (BitVec 64)),
    Writable s (rspOf s + i) 8
  writable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    Writable s (outputPtr s + i) 8
  stackCodeApart : ∀ i ∈ ([16,24,32,40] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 0x10174c 69
  codeApart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    RangeApart (outputPtr s + i) 8 0x10174c 69
  apart : ∀ i ∈ ([16,24,32,40] : List (BitVec 64)),
    ∀ j ∈ ([0,8,16,24] : List (BitVec 64)),
      RangeApart (rspOf s + i) 8 (outputPtr s + j) 8

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x90,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x28,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0x89,0x4c,0x24,0x20,0x48,0x8b,0x54,0x24,0x78,0x48,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x48,0x89,0x74,0x24,0x18,0x48,0x89,0x54,0x24,0x10,0x48,0x8b,0x7c,0x24,0x60,0x48,0x89,0x47,0x18,0x48,0x89,0x4f,0x10,0x48,0x89,0x77,0x8,0x48,0x89,0x17]

def effect (s : RamState) : Effect :=
  { rip := 0x101791
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 144) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 136) 64⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (rspOf s + 120) 64⟩,
      ⟨(.reg 6 : Operand 64), memLoad s.external (rspOf s + 128) 64⟩,
      ⟨(.reg 7 : Operand 64), outputPtr s⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), memLoad s.external (rspOf s + 144) 64⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), memLoad s.external (rspOf s + 136) 64⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), memLoad s.external (rspOf s + 128) 64⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), memLoad s.external (rspOf s + 120) 64⟩,
      ⟨(.mem (outputPtr s + 24) : Operand 64), memLoad s.external (rspOf s + 144) 64⟩,
      ⟨(.mem (outputPtr s + 16) : Operand 64), memLoad s.external (rspOf s + 136) 64⟩,
      ⟨(.mem (outputPtr s + 8) : Operand 64), memLoad s.external (rspOf s + 128) 64⟩,
      ⟨(.mem (outputPtr s + 0) : Operand 64), memLoad s.external (rspOf s + 120) 64⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10174c bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x174c bytes
    (by decide) (by decide +kernel)

set_option maxHeartbeats 2400000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10174c bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10174c 0x48 (by constructor <;> decide) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 144 (by simp)⟩
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x1754 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101754 0x48 (by constructor <;> decide) 0 (.sib 4 none 0 (.d8 40))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.stackWritable 40 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.stackCodeApart 40 (by simp) a ha (8+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.stackCodeApart 40 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1759 (by decide))
  advance_then (mov_r64_m64_effect_step 0x101759 0x48 (by constructor <;> decide) 1
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1761 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101761 0x48 (by constructor <;> decide) 1 (.sib 4 none 0 (.d8 32))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.stackWritable 32 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.stackCodeApart 32 (by simp) a ha (21+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.stackCodeApart 32 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1766 (by decide))
  advance_then (mov_r64_m64_effect_step 0x101766 0x48 (by constructor <;> decide) 2
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.readable 120 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x176b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10176b 0x48 (by constructor <;> decide) 6
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1773 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101773 0x48 (by constructor <;> decide) 6 (.sib 4 none 0 (.d8 24))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.stackWritable 24 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.stackCodeApart 24 (by simp) a ha (39+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.stackCodeApart 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1778 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101778 0x48 (by constructor <;> decide) 2 (.sib 4 none 0 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 44 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.stackWritable 16 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.stackCodeApart 16 (by simp) a ha (44+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.stackCodeApart 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x177d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10177d 0x48 (by constructor <;> decide) 7
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 49 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1782 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101782 0x48 (by constructor <;> decide) 0 (.base 7 (.d8 24))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 54 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.writable 24 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.codeApart 24 (by simp) a ha (54+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.codeApart 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1786 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x101786 0x48 (by constructor <;> decide) 1 (.base 7 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 58 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.writable 16 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.codeApart 16 (by simp) a ha (58+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.codeApart 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x178a (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10178a 0x48 (by constructor <;> decide) 6 (.base 7 (.d8 8))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 62 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.writable 8 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.codeApart 8 (by simp) a ha (62+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.codeApart 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x178e (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10178e 0x48 (by constructor <;> decide) 2 (.base 7 (.none))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10174c bytes 66 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [external_write_reg, external_write_mem]
      exact hP.writable 0 (by simp)
    · x86_norm [external_write_reg, external_write_mem]
      intro a ha b hb
      have separate := hP.codeApart 0 (by simp) a ha (66+b) (by omega)
      simpa only [outputPtr, rspOf, Operand.read, BitVec.ofNat_eq_ofNat,
        BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [external_write_reg, external_write_mem]
      exact hP.codeApart 0 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1791 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have apart (i : BitVec 64) (hi : i ∈ ([16,24,32,40] : List (BitVec 64)))
      (j : BitVec 64) (hj : j ∈ ([0,8,16,24] : List (BitVec 64))) :
      RangeApart (outputPtr s + j) 8 (rspOf s + i) 8 := by
    intro a ha b hb eq
    exact hp.apart i hi j hj b hb a ha eq.symm
  x86_norm [outputPtr] at apart
  apply hh.weaken
  · x86_norm [effect, outputPtr, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart]
  · x86_norm [effect, outputPtr, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart]
  · intro i
    cases i <;> x86_norm [effect, outputPtr, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart]
  · x86_norm [effect, outputPtr, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart]

end Hkdf.Proofs.Standard.Extract.Copy
