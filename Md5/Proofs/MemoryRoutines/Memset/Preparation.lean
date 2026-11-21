import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Alignment
import Md5.Proofs.MemoryRoutines.Register.Compose
import Md5.Proofs.MemoryRoutines.Register.Cmov

namespace Md5.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block
open Md5.Proofs.MemoryRoutines.Register

abbrev r8 : Operand 64 := .reg 8

def Outside (boundary : ReturnBoundary) : Prop :=
  boundary.rip.toNat < 0x102460 ∨ 0x1024a5 ≤ boundary.rip.toNat

theorem Outside.ne {boundary : ReturnBoundary} (h : Outside boundary)
    {p : BitVec 64} (hlo : 0x102460 ≤ p.toNat) (hhi : p.toNat < 0x1024a5) :
    p ≠ boundary.rip := by
  intro he
  subst p
  unfold Outside at h
  omega

def countsBytes : List UInt8 :=
  [0x49, 0x29, 0xc8, 0x4c, 0x89, 0xc6, 0x48, 0xc1, 0xee, 0x03, 0x41, 0x83, 0xe0, 0x07]

def countsEffect (s : RamState) : Effect :=
  { rip := 0x102494
    writes := [⟨rsi, (r8.read s - rcx.read s) >>> 3⟩,
      ⟨r8, (((r8.read s - rcx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem counts_prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102486)
      (codeRange 0x102486 countsBytes) countsEffect := by
  unfold countsBytes
  md5_run_begin sub_r64_r64_effect_step 0x102486 0x49 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact hb.ne (p := 0x102489) (by decide) (by decide)
  md5_run_then mov_r64_r64_effect_step 0x102489 0x4c 0xc6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102486) (all := countsBytes) 3 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x10248c) (by decide) (by decide)
  md5_run_then shr_r64_imm8_effect_step 0x10248c 0x48 0xee 0x03
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102486) (all := countsBytes) 6 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102490) (by decide) (by decide)
  md5_run_then and_r32_imm8_rex_effect_step 0x102490 0x41 0xe0 7
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102486) (all := countsBytes) 10 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102494) (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [countsEffect]
  · x86_norm [countsEffect, r8]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [countsEffect]
  · x86_norm [countsEffect, r8]

def alignmentBytes : List UInt8 :=
  [0x89, 0xd1, 0xf7, 0xd9, 0x83, 0xe1, 0x07, 0x49, 0x39, 0xc8]

def alignmentEffect (s : RamState) : Effect :=
  let head := ((-(rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64
  { rip := 0x102482
    writes := [⟨rcx, head⟩]
    flags := some (.ofStatusFlags (cmpSpec (r8.read s) head)) }

theorem alignment_prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102478)
      (codeRange 0x102478 alignmentBytes) alignmentEffect := by
  unfold alignmentBytes
  md5_run_begin mov_r32_r32_effect_step 0x102478 0xd1 (by decide)
  case boundary => intro _ _; exact hb.ne (p := 0x10247a) (by decide) (by decide)
  md5_run_then neg_ecx_effect_step 0x10247a
  case sub => exact codeRange_mem_of_drop (p := 0x102478) (all := alignmentBytes) 2 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x10247c) (by decide) (by decide)
  md5_run_then and_r32_imm8_effect_step 0x10247c 0xe1 7 (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102478) (all := alignmentBytes) 4 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x10247f) (by decide) (by decide)
  md5_run_then cmp_r64_r64_effect_step 0x10247f 0x49 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x102478) (all := alignmentBytes) 7 (by decide +kernel)
  case boundary => intro _ _; exact hb.ne (p := 0x102482) (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [alignmentEffect]
  · x86_norm [alignmentEffect, rdx, r8]
    simp [Operand.read, gprNumber, modrmReg]
  · intro i; cases i <;> x86_norm [alignmentEffect, rdx, r8] <;>
      simp [Operand.read, gprNumber, modrmReg, modrmRm, rexB]
  · x86_norm [alignmentEffect, rdx, r8]

def selectBytes : List UInt8 := alignmentBytes ++ [0x49, 0x0f, 0x42, 0xc8]

def selectedCount (s : RamState) : BitVec 64 :=
  let head := ((-(rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64
  if (r8.read s).toNat < head.toNat then r8.read s else head

def selectEffect (s : RamState) : Effect :=
  { rip := 0x102486
    writes := [⟨rcx, selectedCount s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem selectedCount_toNat (s : RamState) :
    (selectedCount s).toNat = alignmentPrefix (rdx.read s) (r8.read s).toNat := by
  unfold selectedCount alignmentPrefix
  dsimp only
  split <;> rename_i h
  · rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at h
    exact (Nat.min_eq_left (Nat.le_of_lt h)).symm
  · rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at h ⊢
    exact (Nat.min_eq_right (Nat.le_of_not_lt h)).symm

theorem select_prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102478)
      (codeRange 0x102478 selectBytes) selectEffect := by
  intro s hr hc hip
  have hsub : ∀ x ∈ codeRange 0x102478 alignmentBytes,
      x ∈ codeRange 0x102478 selectBytes := by
    exact codeRange_mem_of_take (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := alignment_prepare boundary hb s hr (hc.mono hsub) hip
  have hc' : CodeIn (codeRange 0x102478 selectBytes) t :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [alignmentEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hc
  obtain ⟨u, hu, hru, hcu⟩ := (cmovb_rcx_r8_effect_step 0x102482).advances ht
    (hc'.mono (codeRange_mem_of_drop (p := 0x102478) (all := selectBytes) 10
      (by decide +kernel))) he.rip (hb.ne (p := 0x102486) (by decide) (by decide))
  have hrcx : rcx.read t = ((-(rdx.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64 :=
    he.writes
  have hr8 : r8.read t = r8.read s := he.agrees.read (by simp [alignmentEffect,
    Effect.components, Write.component, Operand.component])
  have hcf : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
      decide ((r8.read s).toNat < (((-(rdx.read s).setWidth 32) &&&
        (7 : BitVec 32)).setWidth 64).toNat) := he.flags.1
  have huwrite : rcx.read u = selectedCount s := by
    have hw := hcu.writes
    change rcx.read u = (if (StatusFlags.ofRFLAGS t.RFLAGS).CF then r8.read t else rcx.read t) at hw
    rw [hw, hr8, hrcx, hcf]
    simp [selectedCount]
  have huagree : AgreesExcept (selectEffect s).components s u := by
    apply (he.agrees.trans hcu.agrees).mono
    simp [alignmentEffect, selectEffect, cmovbR64R64Effect, Effect.components,
      Write.component, Operand.component]
  have hue : (selectEffect s).Holds s u := ⟨hcu.rip, huwrite,
    by simp [selectEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows], huagree⟩
  exact ⟨n + 1, u, ha.trans hu, hru,
    hue.codeIn (Effect.Avoids.of_noMem (by simp [selectEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hc, hue⟩

end Md5.Proofs.MemoryRoutines.Memset
