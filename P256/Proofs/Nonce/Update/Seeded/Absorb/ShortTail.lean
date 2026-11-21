import P256.Proofs.Nonce.Update.Absorb.Seeded.ShortTail
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.ShortTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic P256.Proofs.Common.Encoding.Parser.LengthCheck
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)

attribute [local x86_local] Update.Absorb.Prefix.TagHead.store_local
attribute [local x86_compose] cmpR64M64Effect jccEffect branchEffect branchTarget

@[local x86_local] theorem compare_local (p : BitVec 64) :
    Effect.Local (cmpR64M64Effect p 5 5 (fun s => rspOf s + 80)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpR64M64Effect, rspOf, h.read_reg, h.read_mem]
  · intro s
    simp [cmpR64M64Effect, Write.Full, Operand.Full]

@[local x86_local_on] theorem jcc_zero_local (p : BitVec 64) (len : Nat) (off : BitVec 64)
    {cc : BitVec 4} (hcc : cc = 4 ∨ cc = 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.ZF] (jccEffect p len cc off) := by
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro s t h hf
    have hz : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = (StatusFlags.ofRFLAGS t.RFLAGS).ZF := hf .ZF (by simp)
    rcases hcc with rfl | rfl <;> simp [jccEffect, branchEffect, condHolds, hz]
  · intro s
    simp [jccEffect, branchEffect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a76c
  readable : MemReadable s (rspOf s + 80) 8
  writable : MemWritable s (rspOf s + 383) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 383) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x44, 0x0, 0xf3, 0x4c, 0x8d, 0xb4, 0x24, 0x80, 0x1, 0x0, 0x0, 0x88, 0x9c, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x48, 0x83, 0xc5, 0x10, 0x48, 0x3b, 0x6c, 0x24, 0x50, 0xf, 0x84, 0xbc, 0x0, 0x0, 0x0]

def sum (s : RamState) : BitVec 8 :=
  (Operand.reg 3 : Operand 8).read s + (Operand.reg 14 : Operand 8).read s

def atEnd (s : RamState) : Bool :=
  ((Operand.reg 5 : Operand 64).read s + 16) == memLoad s.external (rspOf s + 80) 64

def target (s : RamState) : BitVec 64 := if atEnd s then 0x10a849 else 0x10a78d

def effect (s : RamState) : Effect :=
  { rip := target s
    writes := [⟨(.reg 3 : Operand 64), mergeGPR 8 (sum s) ((Operand.reg 3 : Operand 64).read s)⟩,
      ⟨(.reg 14 : Operand 64), rspOf s + 384⟩,
      ⟨(.mem (rspOf s + 383) : Operand 8), sum s⟩,
      ⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 5 : Operand 64).read s + 16)
      (memLoad s.external (rspOf s + 80) 64))) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a76c bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa76c bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a76c bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (addR8R8Effect 0x10a76c 3 14) from
    add_r8_r8_rex_effect_step 0x10a76c 0x44 0xf3 (by simp [RexPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa76f (by decide))
  advance_then (lea_r64_effect_step 0x10a76f 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a76c bytes 3 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa777 (by decide))⟩
  advance_then (mov_m8_r8_legacy_effect_step 0x10a777 3 (by decide) (.sib 4 none 0 (.d32 383))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a76c bytes 11 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.codeApart 0xa777 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xa76c 33 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa77e (by decide))
  advance_then (show StepEffect _ _ (addR64Imm8Effect 0x10a77e 5 16) from
    add_r64_imm8_effect_step 0x10a77e 0x48 0xc5 16 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a76c bytes 18 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa782 (by decide))⟩
  advance_then (show StepEffect _ _ (cmpR64M64Effect 0x10a782 5 5 (fun s => rspOf s + 80)) from
    cmp_r64_m64_effect_step 0x10a782 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 80))
      (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a76c bytes 22 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers, cmpR64M64Effect, Effect.components]) _, ?_⟩
    · x86_norm
      exact hP.readable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa787 (by decide))
  advance_then_on [.ZF] using (jcc_rel32_effect_step 0x10a787 4 0xbc)
  case sub => exact codeRange_slice_subset 0x10a76c bytes 27 6
  case mid =>
    intro s t hP hH hO hF
    refine ⟨⟨hH.rip_of (by x86_norm), by intro; decide⟩,
      Effect.Avoids.of_noMem (by simp [jccEffect, branchEffect, Effect.components, Component.Covers]) _, ?_⟩
    change (if (StatusFlags.ofRFLAGS t.RFLAGS).ZF then 0x10a849#64 else 0x10a78d#64) ≠ boundary.rip
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa849 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa78d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect, target, atEnd, cmpSpec, subSpec, condHolds, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  · x86_norm [effect, sum, mergeGPR_low8]
    all_goals rfl
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Nonce.Update.Seeded.Absorb.ShortTail

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.CrossTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open P256.Proofs.Common.Encoding.Parser.LengthCheck
open ShortTail (atEnd target)

attribute [local x86_local] ShortTail.compare_local
attribute [local x86_local_on] ShortTail.jcc_zero_local
attribute [local x86_compose] cmpR64M64Effect jccEffect branchEffect branchTarget

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a82a
  readable : MemReadable s (rspOf s + 80) 8

def bytes : List UInt8 :=
  [0x48, 0x83, 0xc5, 0x10, 0x48, 0x3b, 0x6c, 0x24, 0x50, 0xf, 0x85, 0x54, 0xff, 0xff, 0xff, 0xeb, 0xe]

def effect (s : RamState) : Effect :=
  { rip := target s
    writes := [⟨(.reg 5 : Operand 64), (Operand.reg 5 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 5 : Operand 64).read s + 16)
      (memLoad s.external (rspOf s + 80) 64))) }

def prefixEffect (s : RamState) : Effect :=
  { effect s with rip := if atEnd s then 0x10a839 else 0x10a78d }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a82a bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa82a bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem prefix_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a82a bytes) (Effect.post prefixEffect) := by
  advance_begin (show StepEffect _ _ (addR64Imm8Effect 0x10a82a 5 16) from
    add_r64_imm8_effect_step 0x10a82a 0x48 0xc5 16 (by simp [RexWPrefix]) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa82e (by decide))
  advance_then (show StepEffect _ _ (cmpR64M64Effect 0x10a82e 5 5 (fun s => rspOf s + 80)) from
    cmp_r64_m64_effect_step 0x10a82e 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 80))
      (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a82a bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers, cmpR64M64Effect, Effect.components]) _, ?_⟩
    · x86_norm
      exact hP.readable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa833 (by decide))
  advance_then_on [.ZF] using (jcc_rel32_effect_step 0x10a833 5 0xffffff54)
  case sub => exact codeRange_slice_subset 0x10a82a bytes 9 6
  case mid =>
    intro s t hP hH hO hF
    refine ⟨⟨hH.rip_of (by x86_norm), by intro; decide⟩,
      Effect.Avoids.of_noMem (by simp [jccEffect, branchEffect, Effect.components, Component.Covers]) _, ?_⟩
    change (if !(StatusFlags.ofRFLAGS t.RFLAGS).ZF then 0x10a78d#64 else 0x10a839#64) ≠ boundary.rip
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa78d (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa839 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prefixEffect, effect, atEnd, cmpSpec, subSpec, condHolds,
      BitVec.sub_eq_iff_eq_add, BitVec.zero_add, Bool.not_eq_true', Bool.eq_false_iff,
      ite_not]
  · x86_norm [prefixEffect, effect]
  · intro i
    cases i <;> x86_norm [prefixEffect, effect]
  · x86_norm [prefixEffect, effect]

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a82a bytes) (Effect.post effect) := by
  intro s ready loaded pre
  obtain ⟨n, t, run, readyT, loadedT, held⟩ := prefix_run boundary outside s ready loaded pre
  by_cases last : atEnd s = true
  · have ip : t.RIP = 0x10a839 := by simpa only [prefixEffect, last, ↓reduceIte] using held.rip
    obtain ⟨u, step, readyU, jump⟩ := (jmp_rel8_effect_step 0x10a839 0xe (by decide)).advances
      readyT (loadedT.mono (codeRange_slice_subset 0x10a82a bytes 15 2)) ip
      (boundary_ne_program outside (inProgram_of_textOffset 0xa849 (by decide)))
    have agrees : AgreesExcept [.rip] t u := jump.agrees
    have result : (effect s).Holds s u := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have ipU : u.RIP = 0x10a849 := jump.rip
        simpa only [effect, target, last, ↓reduceIte] using ipU
      · exact (agrees.read (n := 64) (r := 5) (by simp)).trans held.writes
      · change StatusFlagsOutcome.Allows _ (StatusFlags.ofRFLAGS u.RFLAGS)
        rw [agrees.rflags (by simp) (by simp)]
        exact held.flags
      · exact (held.agrees.trans agrees).mono (by simp [effect, prefixEffect, Effect.components])
    exact ⟨n+1, u, run.trans step, readyU,
      jump.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) loadedT, result⟩
  · refine ⟨n, t, run, readyT, loadedT, ?_⟩
    simpa only [Effect.post, prefixEffect, effect, target, last, Bool.false_eq_true, ↓reduceIte] using held

end P256.Proofs.Nonce.Update.Seeded.Absorb.CrossTail
