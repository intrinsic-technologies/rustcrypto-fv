import Sha1.Proofs.Streaming.Invariant
import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Frame
import Sha1.Proofs.Compress.Machine.Segment
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Streaming.UpdateFinalize
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.DigestPrepare.Initialize

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read pushAddr_eq_read BitVec.sub_eq_add_neg
  movM8Imm8Effect movM32Imm32Effect subR64Imm32Effect

private def initBytes : List UInt8 := [
  0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
  0x48, 0x81, 0xec, 0x38, 0x01, 0, 0,
  0x48, 0x89, 0x8c, 0x24, 0xc0, 0, 0, 0,
  0x48, 0x89, 0x94, 0x24, 0xd0, 0, 0, 0,
  0x48, 0x89, 0xbc, 0x24, 0xc8, 0, 0, 0,
  0x48, 0xc7, 0x84, 0x24, 0x18, 0x01, 0, 0, 0, 0, 0, 0,
  0x48, 0xb8, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
  0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0, 0,
  0x48, 0xb8, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
  0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0, 0,
  0xc7, 0x84, 0x24, 0x30, 0x01, 0, 0, 0xf0, 0xe1, 0xd2, 0xc3,
  0xc6, 0x84, 0x24, 0x17, 0x01, 0, 0, 0]

private abbrev EntryFrame := PrologueFrame 0x101c30 704

private def savedWords (s : RamState) : List Write :=
  [⟨(.mem (stackPtr s - 8) : Operand 64), s.regValue .rbp⟩,
   ⟨(.mem (stackPtr s - 16) : Operand 64), s.regValue .r15⟩,
   ⟨(.mem (stackPtr s - 24) : Operand 64), s.regValue .r14⟩]

private def saveRegistersEffect (s : RamState) : Effect where
  rip := 0x101c35
  writes := savedWords s ++ [⟨(.reg 4 : Operand 64), stackPtr s - 24⟩]

private def saveEffect (s : RamState) : Effect where
  rip := 0x101c41
  writes := savedWords s ++
    [⟨(.mem (stackPtr s - 32) : Operand 64), s.regValue .r13⟩,
     ⟨(.mem (stackPtr s - 40) : Operand 64), s.regValue .r12⟩,
     ⟨(.mem (stackPtr s - 48) : Operand 64), s.regValue .rbx⟩,
     ⟨(.reg 4 : Operand 64), stackPtr s - 360⟩]
  flags := some ⟨none, none, none, none, none, none⟩

private def pointerEffect (s : RamState) : Effect :=
  { saveEffect s with
    rip := 0x101c65
    writes := (saveEffect s).writes ++
      [⟨(.mem (stackPtr s - 168) : Operand 64), s.regValue .rcx⟩,
       ⟨(.mem (stackPtr s - 152) : Operand 64), s.regValue .rdx⟩,
       ⟨(.mem (stackPtr s - 160) : Operand 64), s.regValue .rdi⟩,
       ⟨(.mem (stackPtr s - 80) : Operand 64), 0⟩] }

private def initLowEffect (s : RamState) : Effect :=
  { pointerEffect s with
    rip := 0x101c81
    writes := (pointerEffect s).writes ++
      [⟨(.mem (stackPtr s - 72) : Operand 64), 0xefcdab8967452301⟩,
       ⟨(.reg 0 : Operand 64), 0x1032547698badcfe⟩] }

private def initEffect (s : RamState) : Effect :=
  { initLowEffect s with
    rip := 0x101c9c
    writes := (initLowEffect s).writes ++
      [⟨(.mem (stackPtr s - 64) : Operand 64), 0x1032547698badcfe⟩,
       ⟨(.mem (stackPtr s - 56) : Operand 32), 0xc3d2e1f0⟩,
       ⟨(.mem (stackPtr s - 81) : Operand 8), 0⟩] }

attribute [local x86_compose] savedWords

private theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

private theorem movM32Imm32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 32} : Effect.Local (movM32Imm32Effect p len am imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [movM32Imm32Effect, storeEffect, AddrMode.addr_obs h]
  · exact congrArg some hi
  · simp [movM32Imm32Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] movM8Imm8Effect_local movM32Imm32Effect_local

macro "init_slot" h:ident "[" off:term "," len:term "," pc:term "," size:term "]" : tactic =>
  `(tactic| (
    try sha1_norm
    first
    | (simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.reduceNeg,
          BitVec.ofNat_eq_ofNat] using
        ($h).writable $off $len (by decide +kernel) (by decide))
    | (simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.reduceNeg,
          BitVec.ofNat_eq_ofNat, Extracted.textAddress, BitVec.reduceAdd,
          Bytes.Chunked.toListFrom, List.length_map, List.length_range'] using
        ($h).apart $off $len (by decide +kernel) (by decide) _ _
          (prologue_text_sub $pc $size (by decide +kernel)))))

macro "init_mid" "[" off:term "," len:term "," pc:term "," size:term "]" : tactic =>
  `(tactic| (
    intro s t h hE hO
    refine ⟨storePre_of_holds hE (hO true) (by sha1_norm) (by x86_addr_obs) ?_ ?_,
      Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · init_slot h [$off, $len, $pc, $size]
    · init_slot h [$off, $len, $pc, $size]
    · apply Effect.avoids_codeRange
      sha1_norm
      try simp only [x86_pre_simp]
      init_slot h [$off, $len, 0x1c30, 108]))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
private theorem save_registers_advances [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ i < 109, (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) saveRegistersEffect := by
  sha1_run_begin_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_effect_step
    0x101c30 0x55 (by decide))
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩ <;> init_slot h [8, 8, 0x1c30, 1]
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    sha1_norm
    try simp only [x86_pre_simp]
    init_slot h [8, 8, 0x1c30, 108]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x101c31 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
  case mid => init_mid [16, 8, 0x1c31, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x101c33 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
  case mid => init_mid [24, 8, 0x1c33, 2]
  sha1_run_finish [saveRegistersEffect]

attribute [local x86_compose] saveRegistersEffect

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
private theorem save_advances [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ i < 109, (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) saveEffect := by
  suffices h : AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) saveRegistersEffect → _ from
    h (save_registers_advances boundary hne)
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x101c35 0x41 0x55 (by unfold RexPrefix; decide) (by decide))
  case mid => init_mid [32, 8, 0x1c35, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x101c37 0x41 0x54 (by unfold RexPrefix; decide) (by decide))
  case mid => init_mid [40, 8, 0x1c37, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_effect_step 0x101c39 0x53 (by decide))
  case mid => init_mid [48, 8, 0x1c39, 1]
  sha1_run_then (sub_r64_imm32_effect_step 0x101c3a 0x48 0xec 312
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  sha1_run_finish [saveEffect]

attribute [local x86_compose] saveEffect

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
private theorem pointer_advances [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ i < 109, (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) pointerEffect := by
  suffices h : AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) saveEffect → _ from
    h (save_advances boundary hne)
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x101c41 0x48
    (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 192))
    (by decide) (by decide) (by decide))
  case mid => init_mid [168, 8, 0x1c41, 8]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x101c49 0x48
    (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 208))
    (by decide) (by decide) (by decide))
  case mid => init_mid [152, 8, 0x1c49, 8]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x101c51 0x48
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 200))
    (by decide) (by decide) (by decide))
  case mid => init_mid [160, 8, 0x1c51, 8]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_imm32_effect_step 0x101c59 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 280))
    (by decide) (by decide) (by decide) 0)
  case mid => init_mid [80, 8, 0x1c59, 12]
  sha1_run_finish [pointerEffect]

attribute [local x86_compose] pointerEffect

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
private theorem init_low_advances [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ i < 109, (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) initLowEffect := by
  suffices h : AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) pointerEffect → _ from
    h (pointer_advances boundary hne)
  sha1_run_then (mov_r64_imm64_effect_step 0x101c65 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0xefcdab8967452301)
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x101c6f 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 288))
    (by decide) (by decide) (by decide))
  case mid => init_mid [72, 8, 0x1c6f, 8]
  sha1_run_then (mov_r64_imm64_effect_step 0x101c77 0x48 0xb8
    (by unfold RexWPrefix; decide) (by decide) 0x1032547698badcfe)
  sha1_run_finish [initLowEffect]

attribute [local x86_compose] initLowEffect

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
private theorem init_advances [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ i < 109, (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) initEffect := by
  suffices h : AdvancesBlock boundary EntryFrame (codeRange 0x101c30 initBytes) initLowEffect → _ from
    h (init_low_advances boundary hne)
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x101c81 0x48
    (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 296))
    (by decide) (by decide) (by decide))
  case mid => init_mid [64, 8, 0x1c81, 8]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_imm32_effect_step 0x101c89
    (.sib 4 none 0 (.d32 304)) (by decide) (by decide) (by decide) 0xc3d2e1f0)
  case mid => init_mid [56, 4, 0x1c89, 11]
  sha1_run_then_manual (Sha1.Proofs.Buffered.DigestPrepare.Initialize.mov_m8_imm8_effect_step 0x101c94
    (.sib 4 none 0 (.d32 279)) (by decide) (by decide) (by decide) 0)
  case mid => init_mid [81, 1, 0x1c94, 8]
  sha1_run_finish [initEffect]

private def branchChanges : List Component := [.reg 12, .reg 15, .flags, .rip]

private theorem branchChanges_external {s t : RamState}
    (h : AgreesExcept branchChanges s t) : t.external = s.external :=
  h.external (by simp [branchChanges, Component.Covers])

private theorem enter_header [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x101c9c) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      AgreesExcept branchChanges s t ∧
      t.RIP = (if s.regValue .rsi = 0 then 0x101dcb else 0x101cdd) ∧
      (s.regValue .rsi ≠ 0 → t.regValue .r15 = 0 ∧ t.regValue .r12 = s.regValue .rsi) := by
  have hne (offset : Nat) (h : offset < Extracted.textBytes.size) :=
    text_address_ne_return hOutside offset h
  obtain ⟨a, ha, hra, hea⟩ :=
    (test_r64_r64_effect_step 0x101c9c 0x48 0xf6
      (by unfold RexWPrefix; decide) (by decide)).advances
      hReady (program_text_slice hCode 0x1c9c 3 (by decide +kernel)) hRip
      (hne 0x1c9f (by decide +kernel))
  have hga : AgreesExcept branchChanges s a :=
    hea.agrees.mono (by simp [branchChanges, testR64R64Effect_components])
  have hza : condHolds 4 (StatusFlags.ofRFLAGS a.RFLAGS) = (s.regValue .rsi == 0) := by
    have hf := hea.flags
    change (testFlags (s.regValue .rsi &&& s.regValue .rsi)).Allows
      (StatusFlags.ofRFLAGS a.RFLAGS) at hf
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = _
    have hz := hf.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at hz
    simpa only [BitVec.and_self] using hz
  have hca := CodeIn.of_external_eq (branchChanges_external hga) hCode
  have hbr : CodeIn (codeRange 0x101c9f (0x0f :: jccOpcode32 4 :: immBytes 32 0x126)) a :=
    program_text_slice hca 0x1c9f 6 (by decide +kernel)
  have hNext : (jccEffect 0x101c9f 6 4 ((0x126 : BitVec 32).signExtend 64) a).rip =
      (if s.regValue .rsi = 0 then 0x101dcb else 0x101ca5) := by
    by_cases hz : s.regValue .rsi = 0 <;>
      simp only [jccEffect, branchEffect, hza, hz, beq_self_eq_true, beq_iff_eq,
        ↓reduceIte] <;> rfl
  obtain ⟨b, hb, hrb, heb⟩ := (jcc_rel32_effect_step 0x101c9f 4 0x126).advances
    hra hbr ⟨hea.rip, fun _ => by decide⟩ (by
      rw [hNext]
      split
      · exact hne 0x1dcb (by decide +kernel)
      · exact hne 0x1ca5 (by decide +kernel))
  have hgb : AgreesExcept branchChanges s b :=
    (hga.trans heb.agrees).mono (by simp [branchChanges, jccEffect, branchEffect_components])
  have hpb := heb.rip.trans hNext
  by_cases hz : s.regValue .rsi = 0
  · refine ⟨2, b, ha.trans hb, hrb, hgb, ?_, fun hn => (hn hz).elim⟩
    simpa only [hz, ↓reduceIte] using hpb
  have hcb := CodeIn.of_external_eq (branchChanges_external hgb) hCode
  obtain ⟨c, hc, hrc, hec⟩ :=
    (mov_r64_r64_effect_step 0x101ca5 0x49 0xf4
      (by unfold RexWPrefix; decide) (by decide)).advances
      hrb (program_text_slice hcb 0x1ca5 3 (by decide +kernel))
      (by simpa only [hz, ↓reduceIte] using hpb) (hne 0x1ca8 (by decide +kernel))
  have hgc : AgreesExcept branchChanges s c :=
    (hgb.trans hec.agrees).mono (by simp [branchChanges, movR64R64Effect_components]; decide)
  have hcc := CodeIn.of_external_eq (branchChanges_external hgc) hCode
  obtain ⟨d, hd, hrd, hed⟩ :=
    (xor_r32_r32_rex_effect_step 0x101ca8 0x45 0xff
      (by unfold RexNoWPrefix; decide) (by decide)).advances
      hrc (program_text_slice hcc 0x1ca8 3 (by decide +kernel))
      hec.rip (hne 0x1cab (by decide +kernel))
  have hgd : AgreesExcept branchChanges s d :=
    (hgc.trans hed.agrees).mono (by
      change ∀ c ∈ branchChanges ++ [.reg 15, .flags, .rip], c ∈ branchChanges
      simp [branchChanges])
  have hcd := CodeIn.of_external_eq (branchChanges_external hgd) hCode
  obtain ⟨t, ht, hrt, het⟩ := (jmp_rel8_effect_step 0x101cab 0x30 (by decide +kernel)).advances
    hrd (program_text_slice hcd 0x1cab 2 (by decide +kernel)) hed.rip
    (hne 0x1cdd (by decide +kernel))
  have hgt : AgreesExcept branchChanges s t :=
    (hgd.trans het.agrees).mono (by simp [branchChanges, jmpEffect_components])
  refine ⟨5, t, (((ha.trans hb).trans hc).trans hd).trans ht, hrt, hgt, ?_, fun _ ↦ ?_⟩
  · have h := het.rip
    change t.RIP = 0x101cdd at h
    simpa only [hz, ↓reduceIte] using h
  · have h15 : (Operand.reg 15 : Operand 64).read d = 0 := by
      have hw := hed.writes
      change (Operand.reg 15 : Operand 64).read d =
        (((Operand.reg 15 : Operand 32).read c) ^^^ ((Operand.reg 15 : Operand 32).read c)).setWidth 64 at hw
      rw [BitVec.xor_self, BitVec.setWidth_zero] at hw
      exact hw
    have h12 : (Operand.reg 12 : Operand 64).read c = (Operand.reg 6 : Operand 64).read b :=
      hec.writes
    change (Operand.reg 15 : Operand 64).read t = 0 ∧
      (Operand.reg 12 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s
    rw [het.agrees.read (by decide), h15, het.agrees.read (by decide),
      hed.agrees.read (by change Component.reg 12 ∉ [Component.reg 15, .flags, .rip]; decide),
      h12, hgb.read (by decide)]
    exact ⟨rfl, rfl⟩

private theorem init_memory {s : RamState} (h : EntryFrame s)
    {c : Component} (hc : c ∈ (initEffect s).components) {a : BitVec 64}
    (ha : c.Covers a) :
    (Stack.region s SliceHash.updateFinalize.minStackBytes).Contains a.toNat ∧
      a.toNat < (stackPtr s).toNat := by
  have inside (offset len : Nat) (ho : offset ≤ SliceHash.updateFinalize.minStackBytes)
      (hl : len ≤ offset) (hcov : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
      (Stack.region s SliceHash.updateFinalize.minStackBytes).Contains a.toNat ∧
        a.toNat < (stackPtr s).toNat := by
    change offset ≤ 704 at ho
    obtain ⟨i, hi, he⟩ := hcov
    have hc := h.slot_contains offset len ho (by omega) i hi
    rw [← he] at hc
    refine ⟨hc, ?_⟩
    have hlo := h.stack.2.2.1
    change 704 ≤ (stackPtr s).toNat at hlo
    have hBound := h.stack.1
    change (stackPtr s).toNat - 704 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 704)) < 2 ^ 32 at hBound
    rw [he, BitVec.toNat_add, h.slot_toNat offset ho, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [initEffect, initLowEffect, pointerEffect, saveEffect, savedWords,
    Effect.components, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.mem_cons, List.not_mem_nil,
    or_false, Nat.reduceDiv] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ha.elim
    | exact inside 8 8 (by decide) (by decide) ha
    | exact inside 16 8 (by decide) (by decide) ha
    | exact inside 24 8 (by decide) (by decide) ha
    | exact inside 32 8 (by decide) (by decide) ha
    | exact inside 40 8 (by decide) (by decide) ha
    | exact inside 48 8 (by decide) (by decide) ha
    | exact inside 168 8 (by decide) (by decide) ha
    | exact inside 152 8 (by decide) (by decide) ha
    | exact inside 160 8 (by decide) (by decide) ha
    | exact inside 80 8 (by decide) (by decide) ha
    | exact inside 72 8 (by decide) (by decide) ha
    | exact inside 64 8 (by decide) (by decide) ha
    | exact inside 56 4 (by decide) (by decide) ha
    | exact inside 81 1 (by decide) (by decide) ha

private theorem init_return {s t : RamState} (h : EntryFrame s)
    (he : (initEffect s).Holds s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip := by
  change memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  apply memLoad_congr
  intro i hi
  apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
  apply he.agrees.byte
  intro c hc hcov
  have hl := (init_memory h hc hcov).2
  have hb := h.stack.1
  change (stackPtr s).toNat - 704 +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 704)) < 2^32 at hb
  rw [toNat_add_ofNat _ _ (by omega)] at hl
  omega

macro "init_read" hsp:term "," hext:term "," hword:term : tactic => `(tactic| (
  try unfold stackWord
  rw [($hsp)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
    BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Operand.read]
  rw [($hext)]
  have hw := $hword
  simp only [BitVec.sub_eq_add_neg, BitVec.reduceNeg, Operand.read] at hw
  exact hw))

set_option maxRecDepth 4096 in
theorem initialize_header [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧ Header initial inputs 0 s := by
  have hEntry : EntryFrame initial :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable,
      (hCall.separation.2 (Stack.region initial SliceHash.updateFinalize.minStackBytes) (by simp)).2⟩
  have hne (i : Nat) (hi : i < 109) :
      (0x101c30 : BitVec 64) + BitVec.ofNat 64 i ≠ (returnBoundary initial).rip := by
    have hn := text_address_ne_return hOutside (0x1c30 + i) (by
      have hSize : 0x1c30 + 109 ≤ Extracted.textBytes.size := by decide +kernel
      omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hn
    exact hn
  obtain ⟨n, s, ha, hReadyS, _, he⟩ := init_advances (returnBoundary initial) hne initial hReady
    (program_text_slice hCode 0x1c30 108 (by decide +kernel)) hEntry
  have hcS := he.codeIn (by
    intro x hx c hc hcov
    exact hEntry.avoids x.1 (init_memory hEntry hc hcov).1 (.inl ⟨x.2, hx⟩)) hCode
  obtain ⟨m, t, hb, hReadyT, hgt, hRip, hCounters⟩ :=
    enter_header hReadyS hcS he.rip hOutside
  have hext := branchChanges_external hgt
  have hsp : stackPtr t = stackPtr initial - 360 := by
    rw [stackPtr_read, hgt.read (by decide)]
    exact he.writes.2.2.2.2.2.2.1
  have hDFs : DirectionFlagUnset s := he.agrees.directionFlagClear (by
    simp [initEffect, initLowEffect, pointerEffect, saveEffect, savedWords, Effect.components]) hCall.directionFlagUnset
  have hDFt : DirectionFlagUnset t :=
    hgt.directionFlagClear (by decide) hDFs
  have hMW : MemoryWriteFrame initial t #v[Stack.region initial SliceHash.updateFinalize.minStackBytes] := by
    intro a hout
    rw [hext]
    exact he.agrees.memoryWriteFrame
      (fun c hc a hcov => ⟨_, by simp, (init_memory hEntry hc hcov).1⟩) a hout
  have hw := he.writes
  change Write.AllHold s (initEffect initial).writes at hw
  simp only [initEffect, initLowEffect, pointerEffect, saveEffect, savedWords,
    List.cons_append, List.nil_append, Write.AllHold] at hw
  rcases hw with ⟨hRbp, hR15, hR14, hR13, hR12, hRbx, _, hOut, hLens, hPtrs, hBlocks,
    hLow, _, hMid, hHigh, hPosition⟩
  have hReturn := init_return hEntry he
  have hf : Frame initial t := by
    refine ⟨hReadyT, CodeIn.of_external_eq hext hcS, hDFt, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hMW, (he.agrees.trans hgt).grow, (he.agrees.trans hgt).rest⟩
    · init_read hsp, hext, hOut
    · init_read hsp, hext, hPtrs
    · init_read hsp, hext, hLens
    · init_read hsp, hext, hRbx
    · init_read hsp, hext, hR12
    · init_read hsp, hext, hR13
    · init_read hsp, hext, hR14
    · init_read hsp, hext, hR15
    · init_read hsp, hext, hRbp
    · init_read hsp, hext, hReturn
  have hCountNat : (s.regValue .rsi).toNat = inputs.size := by
    have hReg : (Operand.reg 6 : Operand 64).read s = (Operand.reg 6 : Operand 64).read initial :=
      he.agrees.read (by
        simp [initEffect, initLowEffect, pointerEffect, saveEffect, savedWords, Effect.components])
    exact (congrArg BitVec.toNat hReg).trans hCall.sliceCountArgumentMatchesInputs
  have hCount : s.regValue .rsi = BitVec.ofNat 64 inputs.size := by
    rw [← hCountNat, BitVec.ofNat_toNat]
    rfl
  have hz : s.regValue .rsi = 0 ↔ inputs.size = 0 := by
    constructor
    · intro h
      rw [h] at hCountNat
      exact hCountNat.symm
    · intro h
      exact BitVec.eq_of_toNat_eq (hCountNat.trans h)
  refine ⟨n + m, t, ha.trans hb, hf, ?_, ?_, ?_⟩
  · rw [Array.extract_eq_empty_of_le (by simp), Sha1.Proofs.Streaming.message_empty]
    apply absorbed_empty_of_initial_words
    · have hr := (hEntry.writable 72 20 (by decide) (by decide)).readable
      have ht : MemReadable t (stackPtr initial - 72) 20 :=
        ⟨hr.low, fun i hi => (he.agrees.trans hgt).grow _ (hr.mem i hi)⟩
      simpa only [hsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
        BitVec.reduceAdd] using ht
    · init_read hsp, hext, hLow
    · init_read hsp, hext, hMid
    · init_read hsp, hext, hHigh
    · init_read hsp, hext, hPosition
    · init_read hsp, hext, hBlocks
  · rw [hRip]
    simp only [hz]
    by_cases h : inputs.size = 0
    · simp only [h, Nat.lt_irrefl, ↓reduceIte]
    · simp only [h, ↓reduceIte, Nat.pos_of_ne_zero h]
  · intro hi
    obtain ⟨h15, h12⟩ := hCounters (fun h => (Nat.ne_of_gt hi) (hz.mp h))
    exact ⟨h15, h12.trans hCount⟩

end Sha1.Proofs.Entry.UpdateFinalize
