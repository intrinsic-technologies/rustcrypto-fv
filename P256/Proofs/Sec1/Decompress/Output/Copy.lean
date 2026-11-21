import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x11005f
  readable : ∀ i ∈ ([120, 128, 136, 144] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x8c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x4, 0x24, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x11008f
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 144) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 128) 64⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64),
        memLoad s.external ((Operand.reg 4 : Operand 64).read s + 120) 64⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64),
        memLoad s.external ((Operand.reg 4 : Operand 64).read s + 128) 64⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64),
        memLoad s.external ((Operand.reg 4 : Operand 64).read s + 136) 64⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64),
        memLoad s.external ((Operand.reg 4 : Operand 64).read s + 144) 64⟩] }

set_option maxHeartbeats 1000000 in
theorem copy_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x11005f copyBytes) (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11005f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 120 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10064 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110064 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1006c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11006c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 13 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0x1006c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0x1005f 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10070 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110070 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 17 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0x10070 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0x1005f 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10075 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110075 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 22 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1007d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11007d 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x1007d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x1005f 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10082 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110082 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 35 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1008a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11008a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11005f copyBytes 43 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x1008a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x1005f 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1008f (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (apart : OffsetsApart i 8 j 8) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + i) v)
        ((Operand.reg 4 : Operand 64).read s + j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    memLoad_memStore_apart mem ((Operand.reg 4 : Operand 64).read s) i j v 64 apart (by decide) (by decide)
  have h0_136 := fun mem v ↦ hread mem 0 136 v (by unfold OffsetsApart; decide +kernel)
  have h0_144 := fun mem v ↦ hread mem 0 144 v (by unfold OffsetsApart; decide +kernel)
  have h8_136 := fun mem v ↦ hread mem 8 136 v (by unfold OffsetsApart; decide +kernel)
  have h8_144 := fun mem v ↦ hread mem 8 144 v (by unfold OffsetsApart; decide +kernel)
  have h16_136 := fun mem v ↦ hread mem 16 136 v (by unfold OffsetsApart; decide +kernel)
  have h16_144 := fun mem v ↦ hread mem 16 144 v (by unfold OffsetsApart; decide +kernel)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0_136 h0_144 h8_136 h8_144 h16_136 h16_144
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, h0_136, h0_144, h8_136, h8_144, h16_136, h16_144]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]

end P256.Proofs.Sec1.Decompress.Output
