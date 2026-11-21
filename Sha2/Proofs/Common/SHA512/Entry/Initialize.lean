import Sha2.Proofs.Common.SHA512.Entry.Save
import Sha2.Proofs.Common.SHA512.Entry.Frame
import Sha2.Proofs.Common.SHA512.Entry.Memory
import Sha2.Proofs.Common.SHA512.Loop
import Sha2.Proofs.Common.Instructions.ShiftLeft.Compose
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
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
import X86Proofs.Instructions.Movs.RepTriple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Instructions.ShiftLeft

variable [Bindings] {initial : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt64} {input : ByteArray} {count : Nat}

structure PointerPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ddaa
  writable : Sha2.Proofs.Common.Instructions.CrossPageStore.Writable s
    (stackPtr s + 0xe8) 8
  apart : RangeApart (stackPtr s + 0xe8) 8 0x10ddaa 18

def pointerBytes : List UInt8 :=
  [0x48,0x89,0xd0,0x48,0xc1,0xe0,7,0x48,1,0xf0,0x48,0x89,0x84,0x24,0xe8,0,0,0]

def pointerEffect (s : RamState) : Effect :=
  { rip := 0x10ddbc
    writes := [⟨(Operand.reg 0 : Operand 64), (s.regValue .rdx <<< 7) + s.regValue .rsi⟩,
      ⟨(Operand.mem (stackPtr s + 0xe8) : Operand 64),
        (s.regValue .rdx <<< 7) + s.regValue .rsi⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

attribute [local x86_compose] shlR64Effect shlFlags

set_option maxHeartbeats 800000 in
theorem pointer_correct (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary PointerPre (codeRange 0x10ddaa pointerBytes)
      (Effect.post pointerEffect) := by
  advance_begin mov_r64_r64_effect_step 0x10ddaa 0x48 0xd0 (by simp [RexWPrefix]) rfl
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0xddad (by decide))
  advance_then shl_r64_imm8_effect_step 0x10ddad 0x48 0xe0 7 (by simp [RexWPrefix]) rfl rfl
  case loc => exact shlR64Effect_local _ _ _ 7 (by decide)
  case sub => exact codeRange_slice_subset 0x10ddaa pointerBytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, shlR64Effect_components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xddb1 (by decide))⟩
  advance_then add_r64_r64_effect_step 0x10ddb1 0x48 0xf0 (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x10ddaa pointerBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xddb4 (by decide))⟩
  advance_then Sha2.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10ddb4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x10ddaa pointerBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Sha2.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (10 + j) (by omega)
      change stackPtr s + (0xe8 : BitVec 64) + BitVec.ofNat 64 i =
        (0x10ddb4 : BitVec 64) + BitVec.ofNat 64 j at he
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · x86_norm
      exact boundary_ne_program outside (inProgram_of_textOffset 0xddbc (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [pointerEffect]
  · x86_norm [pointerEffect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [pointerEffect]
  · x86_norm [pointerEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

set_option maxHeartbeats 10000000 in
theorem entry_initialize (pre : CompressionPre initial boundary hash input count)
    (positive : 0 < count) :
    ∃ fuel final, Advances boundary fuel initial final ∧ final.RIP = 0x10ddf0 ∧
      LoopState initial final hash 0 count := by
  obtain ⟨s, runS, readyS, loadedS, ripS, rspS, memS, agreesS⟩ := entry_save pre positive
  have frameS := entry_saved_frame pre readyS loadedS rspS memS agreesS
  have ep : PointerPre s := by
    refine ⟨ripS, frameS.stackOffset_writable pre (offset := 0xe8) (by decide), ?_⟩
    apply frameS.stackOffset_codeApart pre (offset := 0xe8) (pos := 0xddaa) (by decide)
    intro j hj
    have h := inProgram_of_textOffset (0xddaa+j) (by omega)
    simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨fuelP, t, runP, readyT, _, effectP⟩ := pointer_correct boundary pre.outerBoundary s readyS
    (programText_slice (programLoaded_codeIn loadedS) 0xddaa pointerBytes
      (by decide) (by decide +kernel)) ep
  have frameT : FrameState initial t := by
    apply frameS.after_agrees pre readyT effectP.agrees
    · simp [pointerEffect, Effect.components]
    · intro c hc a ha
      simp only [pointerEffect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, Write.component] at hc
      rcases hc with hreg | hrest
      · rw [hreg] at ha
        exact ha.elim
      rcases hrest with hmem | hrest
      · rw [hmem] at ha
        exact frameS.stackOffset_local pre (offset := 0xe8) (len := 8) (by decide) ha
      rcases hrest with hflags | hrip
      · rw [hflags] at ha
        exact ha.elim
      · rw [hrip] at ha
        exact ha.elim
    all_goals simp [pointerEffect, Effect.components]
  have hash_read (i : Nat) (hi : i < 8) :
      memLoad t.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i)) 64 =
        memLoad s.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i)) 64 := by
    apply memLoad_congr
    intro j hj
    apply memByte_congr
    apply effectP.agrees.byte
    intro c hc hcov
    simp only [pointerEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, Write.component] at hc
    rcases hc with (rfl | rfl | rfl | rfl)
    · exact hcov.elim
    · obtain ⟨k, hk, he⟩ := hcov
      have hstack : (Stack.region initial 416).Contains
          (stackPtr s + BitVec.ofNat 64 0xe8 + BitVec.ofNat 64 k).toNat := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact frameS.stackOffset_contains pre (by omega)
      have he' : initial.regValue .rdi + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j =
          stackPtr s + BitVec.ofNat 64 0xe8 + BitVec.ofNat 64 k := by
        simpa only [BitVec.ofNat_eq_ofNat] using he
      apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hstack
      rw [← he', BitVec.add_assoc, ← BitVec.ofNat_add]
      exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
        (by change 8 * i + j < 64; omega)
    · exact hcov.elim
    · exact hcov.elim
  have readable0 : MemReadable t (initial.regValue .rdi) 8 := by
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      frameT.hashWord_readable pre (i := 0) (by decide)
  have addr0 : (.base 7 .none : AddrMode).addr t
      ((0x10ddbc : BitVec 64) + BitVec.ofNat 64 3) = t.regValue .rdi := by
    change t.regValue .rdi + 0 = t.regValue .rdi
    simp
  have diT : t.regValue .rdi = initial.regValue .rdi := by
    exact (effectP.agrees.read (n := 64) (r := 7) (by simp [pointerEffect, Effect.components])).trans
      (agreesS.read (n := 64) (r := 7) (by simp [Sha2.Proofs.Common.Encoding.Serialize.saveFrame]))
  have readable0' : MemReadable t (t.regValue .rdi) 8 := by
    rw [diT]
    exact readable0
  obtain ⟨u, run1, ready1, effect1⟩ :=
    (mov_r64_m64_effect_step 0x10ddbc 0x4c (by simp [RexWPrefix]) 3
      (.base 7 .none) (by decide) (by decide) (by decide)).advances readyT
      (programText_slice (programLoaded_codeIn frameT.loaded) 0xddbc
        [0x4c,0x8b,0x1f] (by decide) (by decide +kernel))
      ⟨effectP.rip, addr0 ▸ readable0'⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddbf (by decide)))
  have hreg0 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (3 : BitVec 3) = 11 := by
    decide +kernel
  have frame1 : FrameState initial u :=
    frameT.after_registers ready1 effect1.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word0 : u.regValue .r11 = hash[0]!.toBitVec := by
    have hw := effect1.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (3 : BitVec 3)) : Operand 64).read u = _ at hw
    rw [hreg0] at hw
    have hwraw : BitVec.setWidth 64 u.GPR[gprIndex (11 : BitVec 5)] =
        memLoad t.external
          (BitVec.setWidth 64 t.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 0) 64 := by
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value] using hw
    have haddr : BitVec.setWidth 64 t.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 0 =
        t.regValue .rdi := by
      change t.regValue .rdi + 0 = t.regValue .rdi
      exact BitVec.add_zero _
    rw [haddr] at hwraw
    have hw'' : u.regValue .r11 = memLoad t.external (t.regValue .rdi) 64 := by
      change BitVec.setWidth 64 u.GPR[gprIndex (11 : BitVec 5)] = _
      exact hwraw
    rw [hw'']
    rw [diT]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 0)
      (by decide)
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (hash_read 0 (by decide)).trans hsword
  have diU : u.regValue .rdi = initial.regValue .rdi :=
    (effect1.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diT
  have memoryU : u.external = t.external :=
    effect1.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable1 : MemReadable u (u.regValue .rdi + 8) 8 := by
    rw [diU]
    exact frame1.hashWord_readable pre (i := 1) (by decide)
  have addr1 : (.base 7 (.d8 8) : AddrMode).addr u
      ((0x10ddbf : BitVec 64) + BitVec.ofNat 64 4) = u.regValue .rdi + 8 := by
    rfl
  obtain ⟨v, run2, ready2, effect2⟩ :=
    (mov_r64_m64_effect_step 0x10ddbf 0x48 (by simp [RexWPrefix]) 1
      (.base 7 (.d8 8)) (by decide) (by decide) (by decide)).advances ready1
      (programText_slice (programLoaded_codeIn frame1.loaded) 0xddbf
        [0x48,0x8b,0x4f,0x08] (by decide) (by decide +kernel))
      ⟨effect1.rip, addr1 ▸ readable1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddc3 (by decide)))
  have hreg1 : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (1 : BitVec 3) = 1 := by
    decide +kernel
  have frame2 : FrameState initial v :=
    frame1.after_registers ready2 effect2.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word1 : v.regValue .rcx = hash[1]!.toBitVec := by
    have hw := effect2.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (1 : BitVec 3)) : Operand 64).read v = _ at hw
    rw [hreg1] at hw
    have hwraw : BitVec.setWidth 64 v.GPR[gprIndex (1 : BitVec 5)] =
        memLoad u.external
          (BitVec.setWidth 64 u.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 8) 64 := by
      have hdisp : BitVec.signExtend 64 (8 : BitVec 8) = (8 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 u.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 8 =
        u.regValue .rdi + 8 := by
      change u.regValue .rdi + 8 = u.regValue .rdi + 8
      rfl
    rw [haddr] at hwraw
    have hw' : v.regValue .rcx = memLoad u.external (u.regValue .rdi + 8) 64 := by
      change BitVec.setWidth 64 v.GPR[gprIndex (1 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryU, diU]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 1)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 1 (by decide)).trans hsword

  have diV : v.regValue .rdi = initial.regValue .rdi :=
    (effect2.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diU
  have memoryV : v.external = u.external :=
    effect2.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable2 : MemReadable v (v.regValue .rdi + 16) 8 := by
    rw [diV]
    exact frame2.hashWord_readable pre (i := 2) (by decide)
  have addr2 : (.base 7 (.d8 16) : AddrMode).addr v
      ((0x10ddc3 : BitVec 64) + BitVec.ofNat 64 4) = v.regValue .rdi + 16 := by
    rfl
  obtain ⟨w, run3, ready3, effect3⟩ :=
    (mov_r64_m64_effect_step 0x10ddc3 0x4c (by simp [RexWPrefix]) 2
      (.base 7 (.d8 16)) (by decide) (by decide) (by decide)).advances ready2
      (programText_slice (programLoaded_codeIn frame2.loaded) 0xddc3
        [0x4c,0x8b,0x57,0x10] (by decide) (by decide +kernel))
      ⟨effect2.rip, addr2 ▸ readable2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddc7 (by decide)))
  have hreg2 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (2 : BitVec 3) = 10 := by
    decide +kernel
  have frame3 : FrameState initial w :=
    frame2.after_registers ready3 effect3.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word2 : w.regValue .r10 = hash[2]!.toBitVec := by
    have hw := effect3.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (2 : BitVec 3)) : Operand 64).read w = _ at hw
    rw [hreg2] at hw
    have hwraw : BitVec.setWidth 64 w.GPR[gprIndex (10 : BitVec 5)] =
        memLoad v.external
          (BitVec.setWidth 64 v.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 16) 64 := by
      have hdisp : BitVec.signExtend 64 (16 : BitVec 8) = (16 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 v.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 16 =
        v.regValue .rdi + 16 := by
      change v.regValue .rdi + 16 = v.regValue .rdi + 16
      rfl
    rw [haddr] at hwraw
    have hw' : w.regValue .r10 =
        memLoad v.external (v.regValue .rdi + 16) 64 := by
      change BitVec.setWidth 64 w.GPR[gprIndex (10 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryV, memoryU, diV]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 2)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 2 (by decide)).trans hsword

  have diW : w.regValue .rdi = initial.regValue .rdi :=
    (effect3.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diV
  have memoryW : w.external = v.external :=
    effect3.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable3 : MemReadable w (w.regValue .rdi + 24) 8 := by
    rw [diW]
    exact frame3.hashWord_readable pre (i := 3) (by decide)
  have addr3 : (.base 7 (.d8 24) : AddrMode).addr w
      ((0x10ddc7 : BitVec 64) + BitVec.ofNat 64 4) = w.regValue .rdi + 24 := by
    rfl
  obtain ⟨x, run4, ready4, effect4⟩ :=
    (mov_r64_m64_effect_step 0x10ddc7 0x48 (by simp [RexWPrefix]) 0
      (.base 7 (.d8 24)) (by decide) (by decide) (by decide)).advances ready3
      (programText_slice (programLoaded_codeIn frame3.loaded) 0xddc7
        [0x48,0x8b,0x47,0x18] (by decide) (by decide +kernel))
      ⟨effect3.rip, addr3 ▸ readable3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddcb (by decide)))
  have hreg3 : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (0 : BitVec 3) = 0 := by
    decide +kernel
  have frame4 : FrameState initial x :=
    frame3.after_registers ready4 effect4.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word3 : x.regValue .rax = hash[3]!.toBitVec := by
    have hw := effect4.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (0 : BitVec 3)) : Operand 64).read x = _ at hw
    rw [hreg3] at hw
    have hwraw : BitVec.setWidth 64 x.GPR[gprIndex (0 : BitVec 5)] =
        memLoad w.external
          (BitVec.setWidth 64 w.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 24) 64 := by
      have hdisp : BitVec.signExtend 64 (24 : BitVec 8) = (24 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 w.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 24 =
        w.regValue .rdi + 24 := by
      change w.regValue .rdi + 24 = w.regValue .rdi + 24
      rfl
    rw [haddr] at hwraw
    have hw' : x.regValue .rax =
        memLoad w.external (w.regValue .rdi + 24) 64 := by
      change BitVec.setWidth 64 x.GPR[gprIndex (0 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryW, memoryV, memoryU, diW]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 3)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 3 (by decide)).trans hsword

  have diX : x.regValue .rdi = initial.regValue .rdi :=
    (effect4.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diW
  have memoryX : x.external = w.external :=
    effect4.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable4 : MemReadable x (x.regValue .rdi + 32) 8 := by
    rw [diX]
    exact frame4.hashWord_readable pre (i := 4) (by decide)
  have addr4 : (.base 7 (.d8 32) : AddrMode).addr x
      ((0x10ddcb : BitVec 64) + BitVec.ofNat 64 4) = x.regValue .rdi + 32 := by
    rfl
  obtain ⟨y, run5, ready5, effect5⟩ :=
    (mov_r64_m64_effect_step 0x10ddcb 0x48 (by simp [RexWPrefix]) 3
      (.base 7 (.d8 32)) (by decide) (by decide) (by decide)).advances ready4
      (programText_slice (programLoaded_codeIn frame4.loaded) 0xddcb
        [0x48,0x8b,0x5f,0x20] (by decide) (by decide +kernel))
      ⟨effect4.rip, addr4 ▸ readable4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddcf (by decide)))
  have hreg4 : gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (3 : BitVec 3) = 3 := by
    decide +kernel
  have frame5 : FrameState initial y :=
    frame4.after_registers ready5 effect5.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word4 : y.regValue .rbx = hash[4]!.toBitVec := by
    have hw := effect5.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (3 : BitVec 3)) : Operand 64).read y = _ at hw
    rw [hreg4] at hw
    have hwraw : BitVec.setWidth 64 y.GPR[gprIndex (3 : BitVec 5)] =
        memLoad x.external
          (BitVec.setWidth 64 x.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 32) 64 := by
      have hdisp : BitVec.signExtend 64 (32 : BitVec 8) = (32 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 x.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 32 =
        x.regValue .rdi + 32 := by
      change x.regValue .rdi + 32 = x.regValue .rdi + 32
      rfl
    rw [haddr] at hwraw
    have hw' : y.regValue .rbx =
        memLoad x.external (x.regValue .rdi + 32) 64 := by
      change BitVec.setWidth 64 y.GPR[gprIndex (3 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryX, memoryW, memoryV, memoryU, diX]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 4)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 4 (by decide)).trans hsword

  have diY : y.regValue .rdi = initial.regValue .rdi :=
    (effect5.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diX
  have memoryY : y.external = x.external :=
    effect5.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable5 : MemReadable y (y.regValue .rdi + 40) 8 := by
    rw [diY]
    exact frame5.hashWord_readable pre (i := 5) (by decide)
  have addr5 : (.base 7 (.d8 40) : AddrMode).addr y
      ((0x10ddcf : BitVec 64) + BitVec.ofNat 64 4) = y.regValue .rdi + 40 := by
    rfl
  obtain ⟨z, run6, ready6, effect6⟩ :=
    (mov_r64_m64_effect_step 0x10ddcf 0x4c (by simp [RexWPrefix]) 1
      (.base 7 (.d8 40)) (by decide) (by decide) (by decide)).advances ready5
      (programText_slice (programLoaded_codeIn frame5.loaded) 0xddcf
        [0x4c,0x8b,0x4f,0x28] (by decide) (by decide +kernel))
      ⟨effect5.rip, addr5 ▸ readable5⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddd3 (by decide)))
  have hreg5 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (1 : BitVec 3) = 9 := by
    decide +kernel
  have frame6 : FrameState initial z :=
    frame5.after_registers ready6 effect6.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word5 : z.regValue .r9 = hash[5]!.toBitVec := by
    have hw := effect6.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (1 : BitVec 3)) : Operand 64).read z = _ at hw
    rw [hreg5] at hw
    have hwraw : BitVec.setWidth 64 z.GPR[gprIndex (9 : BitVec 5)] =
        memLoad y.external
          (BitVec.setWidth 64 y.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 40) 64 := by
      have hdisp : BitVec.signExtend 64 (40 : BitVec 8) = (40 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 y.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 40 =
        y.regValue .rdi + 40 := by
      change y.regValue .rdi + 40 = y.regValue .rdi + 40
      rfl
    rw [haddr] at hwraw
    have hw' : z.regValue .r9 =
        memLoad y.external (y.regValue .rdi + 40) 64 := by
      change BitVec.setWidth 64 z.GPR[gprIndex (9 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryY, memoryX, memoryW, memoryV, memoryU, diY]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 5)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 5 (by decide)).trans hsword

  have diZ : z.regValue .rdi = initial.regValue .rdi :=
    (effect6.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diY
  have memoryZ : z.external = y.external :=
    effect6.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have readable6 : MemReadable z (z.regValue .rdi + 48) 8 := by
    rw [diZ]
    exact frame6.hashWord_readable pre (i := 6) (by decide)
  have addr6 : (.base 7 (.d8 48) : AddrMode).addr z
      ((0x10ddd3 : BitVec 64) + BitVec.ofNat 64 4) = z.regValue .rdi + 48 := by
    rfl
  obtain ⟨aa, run7, ready7, effect7⟩ :=
    (mov_r64_m64_effect_step 0x10ddd3 0x4c (by simp [RexWPrefix]) 0
      (.base 7 (.d8 48)) (by decide) (by decide) (by decide)).advances ready6
      (programText_slice (programLoaded_codeIn frame6.loaded) 0xddd3
        [0x4c,0x8b,0x47,0x30] (by decide) (by decide +kernel))
      ⟨effect6.rip, addr6 ▸ readable6⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddd7 (by decide)))
  have hreg6 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (0 : BitVec 3) = 8 := by
    decide +kernel
  have frame7 : FrameState initial aa :=
    frame6.after_registers ready7 effect7.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word6 : aa.regValue .r8 = hash[6]!.toBitVec := by
    have hw := effect7.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (0 : BitVec 3)) : Operand 64).read aa = _ at hw
    rw [hreg6] at hw
    have hwraw : BitVec.setWidth 64 aa.GPR[gprIndex (8 : BitVec 5)] =
        memLoad z.external
          (BitVec.setWidth 64 z.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 48) 64 := by
      have hdisp : BitVec.signExtend 64 (48 : BitVec 8) = (48 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 z.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 48 =
        z.regValue .rdi + 48 := by
      change z.regValue .rdi + 48 = z.regValue .rdi + 48
      rfl
    rw [haddr] at hwraw
    have hw' : aa.regValue .r8 =
        memLoad z.external (z.regValue .rdi + 48) 64 := by
      change BitVec.setWidth 64 aa.GPR[gprIndex (8 : BitVec 5)] = _
      exact hwraw
    rw [hw', memoryZ, memoryY, memoryX, memoryW, memoryV, memoryU, diZ]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 6)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 6 (by decide)).trans hsword

  have diAa : aa.regValue .rdi = initial.regValue .rdi :=
    (effect7.agrees.read (n := 64) (r := 7)
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)).trans diZ
  have memoryAa : aa.external = z.external :=
    effect7.agrees.external (by simp [movR64M64Effect_components, Component.Covers])
  have stateWritable : Sha2.Proofs.Common.Instructions.CrossPageStore.Writable aa
      (stackPtr aa + BitVec.ofNat 64 0xe0) 8 :=
    frame7.stackOffset_writable pre (offset := 0xe0) (by decide)
  have stateApart : RangeApart (stackPtr aa + BitVec.ofNat 64 0xe0) 8
      (0x10ddd7 : BitVec 64) 8 := by
    apply frame7.stackOffset_codeApart pre (offset := 0xe0) (pos := 0xddd7) (by decide)
    intro j hj
    have h := inProgram_of_textOffset (0xddd7 + j) (by omega)
    simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨ac, runS2, readyS2, effectS⟩ :=
    (Sha2.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x10ddd7 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 0xe0))
      (by decide) rfl rfl).advances ready7
      (programText_slice (programLoaded_codeIn frame7.loaded) 0xddd7
        [0x48,0x89,0xbc,0x24,0xe0,0,0,0] (by decide) (by decide +kernel))
      ⟨effect7.rip, stateWritable, stateApart⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdddf (by decide)))
  have frame8 : FrameState initial ac := by
    apply frame7.after_agrees pre readyS2 effectS.agrees
    · simp [movM64R64Effect_components]
    · intro c hc a ha
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hmem | hrip
      · rw [hmem] at ha
        exact frame7.stackOffset_local pre (offset := 0xe0) (len := 8) (by decide) ha
      · rw [hrip] at ha
        exact ha.elim
    all_goals simp [movM64R64Effect_components]
  have diAc : ac.regValue .rdi = initial.regValue .rdi :=
    (effectS.agrees.read (n := 64) (r := 7) (by simp [movM64R64Effect_components])).trans diAa
  have readable7 : MemReadable ac (ac.regValue .rdi + 56) 8 := by
    rw [diAc]
    exact frame8.hashWord_readable pre (i := 7) (by decide)
  have addr7 : (.base 7 (.d8 56) : AddrMode).addr ac
      ((0x10dddf : BitVec 64) + BitVec.ofNat 64 4) = ac.regValue .rdi + 56 := by
    rfl
  obtain ⟨bb, run8, ready8, effect8⟩ :=
    (mov_r64_m64_effect_step 0x10dddf 0x4c (by simp [RexWPrefix]) 5
      (.base 7 (.d8 56)) (by decide) (by decide) (by decide)).advances readyS2
      (programText_slice (programLoaded_codeIn frame8.loaded) 0xdddf
        [0x4c,0x8b,0x6f,0x38] (by decide) (by decide +kernel))
      ⟨effectS.rip, addr7 ▸ readable7⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdde3 (by decide)))
  have hreg7 : gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (5 : BitVec 3) = 13 := by
    decide +kernel
  have frame9 : FrameState initial bb :=
    frame8.after_registers ready8 effect8.agrees
      (by simp [movR64M64Effect_components, Component.Covers])
      (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        decide +kernel)
  have word7 : bb.regValue .r13 = hash[7]!.toBitVec := by
    have hw := effect8.writes
    change (Operand.reg (gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (5 : BitVec 3)) : Operand 64).read bb = _ at hw
    rw [hreg7] at hw
    have hwraw : BitVec.setWidth 64 bb.GPR[gprIndex (13 : BitVec 5)] =
        memLoad ac.external
          (BitVec.setWidth 64 ac.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 56) 64 := by
      have hdisp : BitVec.signExtend 64 (56 : BitVec 8) = (56 : BitVec 64) := by
        decide +kernel
      simpa only [Operand.read, AddrMode.addr, AddrMode.reg64, Disp.value, hdisp] using hw
    have haddr : BitVec.setWidth 64 ac.GPR[gprIndex (BitVec.setWidth 5 (7 : BitVec 4))] + 56 =
        ac.regValue .rdi + 56 := by
      change ac.regValue .rdi + 56 = ac.regValue .rdi + 56
      rfl
    rw [haddr] at hwraw
    have hw' : bb.regValue .r13 = memLoad ac.external (ac.regValue .rdi + 56) 64 := by
      change BitVec.setWidth 64 bb.GPR[gprIndex (13 : BitVec 5)] = _
      exact hwraw
    have stateHash7 :
        memLoad ac.external (initial.regValue .rdi + 56) 64 =
          memLoad aa.external (initial.regValue .rdi + 56) 64 := by
      have he :
          (Operand.mem (initial.regValue .rdi + 56) : Operand 64).read ac =
            (Operand.mem (initial.regValue .rdi + 56) : Operand 64).read aa := by
        apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effectS.agrees
        intro i hi c hc ha
        simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨k, hk, he⟩ := ha
          exact frame7.stackOffset_hashApart pre (offset := 0xe0) (len := 8)
            (by decide) (i := 7) (by decide) k hk i hi he.symm
        · exact ha.elim
      exact he
    rw [hw', diAc, stateHash7, memoryAa, memoryZ, memoryY, memoryX, memoryW, memoryV, memoryU]
    have hsword := entry_saved_hashWord (initial := initial) (current := s) pre agreesS (i := 7)
      (by decide)
    simpa only [BitVec.ofNat_eq_ofNat] using (hash_read 7 (by decide)).trans hsword
  obtain ⟨cc, run9, ready9, effect9⟩ :=
    (nop_m_effect_step 0x10dde3 [0x66,0x66,0x66,0x66,0x2e]
      (by simp [NopPrefix]) (by decide) (.sib 0 (some 0) 0 (.d32 0))
      (by decide) (by decide) (by decide)).advances ready8
      (programText_slice (programLoaded_codeIn frame9.loaded) 0xdde3
        (encodeNopM [0x66,0x66,0x66,0x66,0x2e] (.sib 0 (some 0) 0 (.d32 0)))
        (by decide) (by decide +kernel))
      effect8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xddf0 (by decide)))
  have frame10 : FrameState initial cc :=
    frame9.after_registers ready9 effect9.agrees
      (by simp [nopEffect_components, Component.Covers]) (by simp)
  have siS : s.regValue .rsi = initial.regValue .rsi :=
    agreesS.read (n := 64) (r := 6) (by simp [Sha2.Proofs.Common.Encoding.Serialize.saveFrame])
  have dxS : s.regValue .rdx = BitVec.ofNat 64 count :=
    (agreesS.read (n := 64) (r := 2) (by simp [Sha2.Proofs.Common.Encoding.Serialize.saveFrame])).trans
      pre.countRegister
  have spT : stackPtr t = stackPtr s := effectP.agrees.read (n := 64) (r := 4)
    (by simp [pointerEffect, Effect.components])
  have siT : t.regValue .rsi = initial.regValue .rsi :=
    (effectP.agrees.read (n := 64) (r := 6) (by simp [pointerEffect, Effect.components])).trans siS
  have endT : memLoad t.external (stackPtr t + 0xe8) 64 =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * count) := by
    have hw : memLoad t.external (stackPtr s + 0xe8) 64 =
        (s.regValue .rdx <<< 7) + s.regValue .rsi := effectP.writes.2
    rw [spT, hw, dxS, siS, BitVec.add_comm]
    congr 1
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 count * BitVec.ofNat 64 128 = BitVec.ofNat 64 (128 * count)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have memoryFinal : cc.external = ac.external := by
    rw [effect9.agrees.external (by simp [nopEffect_components, Component.Covers]),
      effect8.agrees.external (by simp [movR64M64Effect_components, Component.Covers])]
  have finalRsp : stackPtr cc = stackPtr ac := by
    have h9 := effect9.agrees.read (n := 64) (r := 4) (by simp [nopEffect_components])
    have h8 := effect8.agrees.read (n := 64) (r := 4) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    change cc.regValue .rsp = bb.regValue .rsp at h9
    change bb.regValue .rsp = ac.regValue .rsp at h8
    exact h9.trans h8
  have statePointer : memLoad cc.external (stackPtr cc + 0xe0) 64 = initial.regValue .rdi := by
    have hs := effectS.writes
    have rspS2 := effectS.agrees.read (n := 64) (r := 4) (by simp [movM64R64Effect_components])
    have rspS2' : ac.regValue .rsp = aa.regValue .rsp := by
      change (Operand.reg (4 : BitVec 5) : Operand 64).read ac = _
      exact rspS2
    have hstate : memLoad ac.external (stackPtr ac + 0xe0) 64 = initial.regValue .rdi := by
      change memLoad ac.external (ac.regValue .rsp + 0xe0) 64 = initial.regValue .rdi
      rw [rspS2']
      exact hs.trans diAa
    rw [memoryFinal, finalRsp]
    exact hstate
  have endAc : memLoad ac.external (stackPtr ac + 0xe8) 64 =
      memLoad t.external (stackPtr t + 0xe8) 64 := by
    have hstack : stackPtr ac = stackPtr aa :=
      effectS.agrees.read (n := 64) (r := 4) (by simp [movM64R64Effect_components])
    rw [hstack]
    have he : memLoad ac.external (stackPtr aa + 0xe8) 64 =
        memLoad aa.external (stackPtr aa + 0xe8) 64 := by
      apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effectS.agrees
      intro i hi c hc hcov
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, he⟩ := hcov
        exact OffsetsApart.ne (c₁ := 0xe0) (len₁ := 8)
          (c₂ := 0xe8) (len₂ := 8) (by unfold OffsetsApart; decide +kernel)
          (stackPtr aa) hj hi (by decide) he.symm
      · exact hcov.elim
    change memLoad ac.external (stackPtr aa + 0xe8) 64 =
      memLoad aa.external (stackPtr aa + 0xe8) 64 at he
    have rspAa : stackPtr aa = stackPtr t := by
      have h7 := effect7.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg6]
        decide +kernel)
      have h6 := effect6.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg5]
        decide +kernel)
      have h5 := effect5.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg4]
        decide +kernel)
      have h4 := effect4.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg3]
        decide +kernel)
      have h3 := effect3.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg2]
        decide +kernel)
      have h2 := effect2.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg1]
        decide +kernel)
      have h1 := effect1.agrees.read (n := 64) (r := 4) (by
        simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
        rw [hreg0]
        decide +kernel)
      change aa.regValue .rsp = z.regValue .rsp at h7
      change z.regValue .rsp = y.regValue .rsp at h6
      change y.regValue .rsp = x.regValue .rsp at h5
      change x.regValue .rsp = w.regValue .rsp at h4
      change w.regValue .rsp = v.regValue .rsp at h3
      change v.regValue .rsp = u.regValue .rsp at h2
      change u.regValue .rsp = t.regValue .rsp at h1
      exact h7.trans (h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1)))))
    rw [he, memoryAa, memoryZ, memoryY, memoryX, memoryW, memoryV, memoryU,
      rspAa, endT]
  have endPointer : memLoad cc.external (stackPtr cc + 0xe8) 64 =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * count) := by
    rw [memoryFinal, finalRsp]
    exact endAc.trans endT
  have inputPointer : cc.regValue .rsi = initial.regValue .rsi := by
    have h9 := effect9.agrees.read (n := 64) (r := 6) (by simp [nopEffect_components])
    have h8 := effect8.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have hs2 := effectS.agrees.read (n := 64) (r := 6) (by
      simp [movM64R64Effect_components])
    have h7 := effect7.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h6 := effect6.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h5 := effect5.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h4 := effect4.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h3 := effect3.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h2 := effect2.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have h1 := effect1.agrees.read (n := 64) (r := 6) (by
      simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
      decide +kernel)
    have hp := effectP.agrees.read (n := 64) (r := 6) (by simp [pointerEffect, Effect.components])
    have h := h9.trans h8
    have h := h.trans hs2
    have h := h.trans h7
    have h := h.trans h6
    have h := h.trans h5
    have h := h.trans h4
    have h := h.trans h3
    have h := h.trans h2
    have h := h.trans h1
    have h := h.trans hp
    exact h.trans siS
  have read9 (r : BitVec 5) :
      (Operand.reg r : Operand 64).read cc = (Operand.reg r : Operand 64).read bb := by
    apply effect9.agrees.read
    simp [nopEffect_components]
  have read8 (r : BitVec 5) (hr : r ≠ 13#5) :
      (Operand.reg r : Operand 64).read bb = (Operand.reg r : Operand 64).read ac := by
    apply effect8.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg7]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have readS (r : BitVec 5) :
      (Operand.reg r : Operand 64).read ac = (Operand.reg r : Operand 64).read aa := by
    apply effectS.agrees.read
    simp [movM64R64Effect_components]
  have read7 (r : BitVec 5) (hr : r ≠ 8#5) :
      (Operand.reg r : Operand 64).read aa = (Operand.reg r : Operand 64).read z := by
    apply effect7.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg6]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read6 (r : BitVec 5) (hr : r ≠ 9#5) :
      (Operand.reg r : Operand 64).read z = (Operand.reg r : Operand 64).read y := by
    apply effect6.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg5]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read5 (r : BitVec 5) (hr : r ≠ 3#5) :
      (Operand.reg r : Operand 64).read y = (Operand.reg r : Operand 64).read x := by
    apply effect5.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg4]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read4 (r : BitVec 5) (hr : r ≠ 0#5) :
      (Operand.reg r : Operand 64).read x = (Operand.reg r : Operand 64).read w := by
    apply effect4.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg3]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read3 (r : BitVec 5) (hr : r ≠ 10#5) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read v := by
    apply effect3.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg2]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read2 (r : BitVec 5) (hr : r ≠ 1#5) :
      (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read u := by
    apply effect2.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg1]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have read1 (r : BitVec 5) (hr : r ≠ 11#5) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read t := by
    apply effect1.agrees.read
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rw [hreg0]
    intro h
    rcases h with h | h
    · apply hr
      cases h
      rfl
    · cases h
  have word0' := word0
  change (Operand.reg (11 : BitVec 5) : Operand 64).read u = _ at word0'
  have word1' := word1
  change (Operand.reg (1 : BitVec 5) : Operand 64).read v = _ at word1'
  have word2' := word2
  change (Operand.reg (10 : BitVec 5) : Operand 64).read w = _ at word2'
  have word3' := word3
  change (Operand.reg (0 : BitVec 5) : Operand 64).read x = _ at word3'
  have word4' := word4
  change (Operand.reg (3 : BitVec 5) : Operand 64).read y = _ at word4'
  have word5' := word5
  change (Operand.reg (9 : BitVec 5) : Operand 64).read z = _ at word5'
  have word6' := word6
  change (Operand.reg (8 : BitVec 5) : Operand 64).read aa = _ at word6'
  have word7' := word7
  change (Operand.reg (13 : BitVec 5) : Operand 64).read bb = _ at word7'
  have combined₁ := runS.trans runP
  have combined₂ := combined₁.trans run1
  have combined₃ := combined₂.trans run2
  have combined₄ := combined₃.trans run3
  have combined₅ := combined₄.trans run4
  have combined₆ := combined₅.trans run5
  have combined₇ := combined₆.trans run6
  have combined₈ := combined₇.trans run7
  have combined₉ := combined₈.trans runS2
  have combined₁₀ := combined₉.trans run8
  have combined := combined₁₀.trans run9
  have nopLen : nopMemLen [0x66,0x66,0x66,0x66,0x2e]
      (.sib 0 (some 0) 0 (.d32 0)) = 13 := by decide
  have finalRip := effect9.rip
  rw [nopLen] at finalRip
  have ripValue : (BitVec.ofNat 64 0x10dde3 + BitVec.ofNat 64 13) =
      (BitVec.ofNat 64 0x10ddf0) := by decide
  have inputPointer' : cc.regValue .rsi =
      initial.regValue .rsi + BitVec.ofNat 64 (128 * 0) := by
    rw [show BitVec.ofNat 64 (128 * 0) = 0#64 from rfl, BitVec.add_zero]
    exact inputPointer
  refine ⟨_, cc, combined, ?_, ?_⟩
  · simpa [nopEffect, ripValue] using finalRip
  refine ⟨frame10, ?_, inputPointer', statePointer, endPointer⟩
  refine ⟨pre.hashWords.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (read9 11).trans (read8 11 (by decide))
    have h := h.trans (readS 11)
    have h := h.trans (read7 11 (by decide))
    have h := h.trans (read6 11 (by decide))
    have h := h.trans (read5 11 (by decide))
    have h := h.trans (read4 11 (by decide))
    have h := h.trans (read3 11 (by decide))
    have h := h.trans (read2 11 (by decide))
    exact h.trans word0'
  · have h := (read9 1).trans (read8 1 (by decide))
    have h := h.trans (readS 1)
    have h := h.trans (read7 1 (by decide))
    have h := h.trans (read6 1 (by decide))
    have h := h.trans (read5 1 (by decide))
    have h := h.trans (read4 1 (by decide))
    have h := h.trans (read3 1 (by decide))
    exact h.trans word1'
  · have h := (read9 10).trans (read8 10 (by decide))
    have h := h.trans (readS 10)
    have h := h.trans (read7 10 (by decide))
    have h := h.trans (read6 10 (by decide))
    have h := h.trans (read5 10 (by decide))
    have h := h.trans (read4 10 (by decide))
    exact h.trans word2'
  · have h := (read9 0).trans (read8 0 (by decide))
    have h := h.trans (readS 0)
    have h := h.trans (read7 0 (by decide))
    have h := h.trans (read6 0 (by decide))
    have h := h.trans (read5 0 (by decide))
    exact h.trans word3'
  · have h := (read9 3).trans (read8 3 (by decide))
    have h := h.trans (readS 3)
    have h := h.trans (read7 3 (by decide))
    have h := h.trans (read6 3 (by decide))
    exact h.trans word4'
  · have h := (read9 9).trans (read8 9 (by decide))
    have h := h.trans (readS 9)
    have h := h.trans (read7 9 (by decide))
    exact h.trans word5'
  · have h := (read9 8).trans (read8 8 (by decide))
    have h := h.trans (readS 8)
    exact h.trans word6'
  · exact (read9 13).trans word7'

end Sha2.Proofs.Common.SHA512
