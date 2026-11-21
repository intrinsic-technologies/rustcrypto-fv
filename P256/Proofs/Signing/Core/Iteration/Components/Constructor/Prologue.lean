import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Input
import P256.Proofs.Program.Push
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
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

open P256.Proofs.Common.Field (AdvanceTriple)

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def entryComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - 8) 8,
    .mem (stackPtr s - 16) 8, .mem (stackPtr s - 24) 8]

theorem stack_setup [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) :
    ∃ t, Advances boundary 4 s t ∧ Frame s t ∧ t.RIP = 0x10989c ∧
      AgreesExcept (entryComponents s) s t := by
  obtain ⟨a, ha, ra, la, ia, pa, fa, ma⟩ :=
    Program.push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 15 0 0x9890
      (by simp) pre.rip (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨b, hb, rb, lb, ib, pb, fb, mb⟩ :=
    Program.push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ra la fa.grow 14 8 0x9892
      pa ia (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨c, hc, rc, lc, ic, pc, fc, mc⟩ :=
    Program.push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary rb lb (fa.trans fb).grow 3 16 0x9894
      pb ib (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨t, ht, rt, et⟩ :=
    (sub_r64_imm32_effect_step 0x109895 0x48 0xec 192
      (by simp [RexWPrefix]) rfl rfl).advances rc
      (programText_slice (programLoaded_codeIn lc) 0x9895 _ (by decide) (by decide +kernel))
      ic (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x989c (by decide)))
  have ft : AgreesExcept [.reg 4, .flags, .rip] c t := et.agrees
  have mt := ft.external (by simp [Component.Covers])
  have f : AgreesExcept (entryComponents s) s t :=
    (((fa.trans fb).trans fc).trans ft).mono (by simp [entryComponents])
  have w : WritesWithin (entryComponents s) #v[registerRegion s .rdi 72, Stack.region s 512] := by
    intro v hv address covered
    simp only [entryComponents, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨_, by simp,
      Program.ScalarFrame.stack_contains pre (by decide) (by decide) covered⟩
  have r14 : (Operand.reg 14 : Operand 64).read a = s.regValue .r14 := fa.read (by simp)
  have rbx : (Operand.reg 3 : Operand 64).read b = s.regValue .rbx := (fa.trans fb).read (by simp)
  have memory : t.external = memStore (memStore (memStore s.external
      (stackPtr s - 8) (s.regValue .r15)) (stackPtr s - 16) (s.regValue .r14))
      (stackPtr s - 24) (s.regValue .rbx) := by
    rw [mt, mc, mb, ma]
    change memStore (memStore (memStore s.external (stackPtr s - 8) (s.regValue .r15))
      (stackPtr s - 16) ((Operand.reg 14 : Operand 64).read a))
      (stackPtr s - 24) ((Operand.reg 3 : Operand 64).read b) = _
    rw [r14, rbx]
  refine ⟨t, ((ha.trans hb).trans hc).trans ht, {
    bindingsSupported := bindingsSupported_of_ready_agrees pre.bindingsSupported rt f
    machine := supportedMachine_of_ready_agrees pre.machine rt f
    loaded := P256.Proofs.Program.ScalarFrame.loaded_of_frame pre (f.memoryWriteFrame w)
    directionFlag := f.directionFlagClear (by component_not_mem) pre.directionFlag
    allocated := f.grow
    frame := f.memoryWriteFrame w
    rsp := ?_
    savedRbx := ?_
    savedR14 := ?_
    savedR15 := ?_
    rbp := f.read (n := 64) (r := 5) (by simp [entryComponents])
    r12 := f.read (n := 64) (r := 12) (by simp [entryComponents])
    r13 := f.read (n := 64) (r := 13) (by simp [entryComponents])
    returnAddress := ?_
    mxcsr := f.mxcsr (by component_not_mem)
    fp87 := f.fcw (by component_not_mem)
  }, et.rip, f⟩
  · have h : stackPtr t = stackPtr c - 192 := et.writes
    rw [h, pc, BitVec.sub_sub]
    rfl
  · change memLoad t.external _ 64 = _
    rw [memory]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad t.external _ 64 = _
    rw [memory]
    simp only [BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ (-24) (-16) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad t.external _ 64 = _
    rw [memory]
    simp only [BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ (-24) (-8) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide),
      memLoad_memStore_apart _ _ (-16) (-8) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad t.external _ 64 = _
    rw [memory]
    simp only [BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart_right _ _ (-24) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide),
      memLoad_memStore_apart_right _ _ (-16) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide),
      memLoad_memStore_apart_right _ _ (-8) _ 64 (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rfl

def entryArgumentBytes : List UInt8 :=
  [0x49,0x89,0xd6,0x48,0x89,0xfb,0x4c,0x8d,0xbc,0x24,0x80,0,0,0,0x4c,0x89,0xff]

def entryArgumentEffect (s : RamState) : Effect :=
  { rip := 0x1098ad
    writes := [⟨(.reg 14 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 15 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 128⟩] }

set_option maxHeartbeats 800000 in
theorem entry_arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10989c) (codeRange 0x10989c entryArgumentBytes)
      (Effect.post entryArgumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10989c 0x49 0xd6 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x989f (by decide))
  advance_then (mov_r64_r64_effect_step 0x10989f 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10989c entryArgumentBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, boundary_ne_program outside (inProgram_of_textOffset 0x98a2 (by decide))⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  advance_then (lea_r64_effect_step 0x1098a2 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10989c entryArgumentBytes 6 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, boundary_ne_program outside (inProgram_of_textOffset 0x98aa (by decide))⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  advance_then (mov_r64_r64_effect_step 0x1098aa 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10989c entryArgumentBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, boundary_ne_program outside (inProgram_of_textOffset 0x98ad (by decide))⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  advance_finish [entryArgumentEffect, stackPtr, Operand.read_reg64]

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x1098ad ∧
      t.regValue .r14 = s.regValue .rdx ∧ t.regValue .r15 = stackPtr t + 128 ∧
      t.regValue .rsi = s.regValue .rsi ∧ t.regValue .rdi = stackPtr t + 128 := by
  obtain ⟨a, ha, state, rip, fa⟩ := stack_setup pre
  obtain ⟨n, t, ht, ready, _, effect⟩ := entry_arguments boundary pre.outerBoundary a
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x989c entryArgumentBytes
      (by decide) (by decide +kernel)) rip
  have f : AgreesExcept [.reg 14, .reg 3, .reg 15, .reg 7, .rip] a t := effect.agrees
  have sp : stackPtr t = stackPtr a := f.read (n := 64) (r := 4) (by simp)
  refine ⟨t, ⟨state.after_registers ready f (by simp [Component.Covers]) (by simp),
    ⟨4+n, ha.trans ht⟩, effect.writes.2.1.trans (fa.read (n := 64) (r := 7) (by simp [entryComponents]))⟩,
    effect.rip, effect.writes.1.trans (fa.read (n := 64) (r := 2) (by simp [entryComponents])),
    ?_, (fa.trans f).read (n := 64) (r := 6) (by simp [entryComponents]), ?_⟩
  · rw [sp]; exact effect.writes.2.2.1
  · rw [sp]; exact effect.writes.2.2.2

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
