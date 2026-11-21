import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Copy

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions.CrossPageStore (Writable)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10dfc6
  readable : ∀ i ∈ ([72,80,88,96,104,112,120] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    Writable s (rspOf s + BitVec.ofNat 64 i) 8
  codeApart : ∀ i ∈ ([8,16,24,32,40,48,56,64] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 85 →
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8
        (0x10dfc6 + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8d, 0x74, 0x24, 0x08, 0xba, 0x01, 0x00, 0x00, 0x00]

def effect (s : RamState) : Effect :=
  { rip := 0x10e01b
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 72) 64⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 8⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.mem (rspOf s + 64) : Operand 64), (.reg 0 : Operand 64).read s⟩] ++
      ([56,48,40,32,24,16,8] : List Nat).map fun i =>
        ⟨(.mem (rspOf s + BitVec.ofNat 64 i) : Operand 64),
          memLoad s.external (rspOf s + BitVec.ofNat 64 (i+64)) 64⟩ }

theorem localEffect : Effect.Local effect := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    have hm (a : BitVec 64) : memLoad s.external a 64 = memLoad t.external a 64 :=
      h.read_mem a
    simp only [effect, rspOf, h.read_reg, hm]
  · intro s
    simp [effect, Write.Full, Operand.Full]

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10dfc6 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xdfc6 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10dfc6 bytes) (Effect.post effect) := by
  advance_begin (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfc6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64))
    (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 64 (by decide), h.codeApart 64 (by decide) 0 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 64 (by decide) 0 85 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xdfcb (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dfcb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfd0 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfd0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by decide)
    · x86_norm
      exact hP.codeApart 56 (by decide) 10 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfd5 (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dfd5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfda (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfda 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by decide)
    · x86_norm
      exact hP.codeApart 48 (by decide) 20 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfdf (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dfdf 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfe4 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfe4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by decide)
    · x86_norm
      exact hP.codeApart 40 (by decide) 30 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfe9 (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dfe9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 96 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdfee (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dfee 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.codeApart 32 (by decide) 40 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdff3 (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dff3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 45 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdff8 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10dff8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 50 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.codeApart 24 (by decide) 50 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdffd (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10dffd 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 55 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 80 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe002 (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10e002 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 60 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.codeApart 16 (by decide) 60 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe007 (by decide))
  advance_then (mov_r64_m64_effect_step
    0x10e007 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 65 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by decide)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe00c (by decide))
  advance_then (Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10e00c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 70 5
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.codeApart 8 (by decide) 70 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by decide) 0 85 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe011 (by decide))
  advance_then (lea_r64_effect_step 0x10e011 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 75 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe016 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10e016 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10dfc6 bytes 80 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe01b (by decide))
  advance_finish [effect, List.map_cons, List.map_nil]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Copy
