import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Instructions.XorImmediate
import Hkdf.Proofs.Common.Instructions.ForgetFlags
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Instructions
open Hkdf.Proofs.Common.Instructions.XorImmediate

local macro "internal " outside:ident offset:term : tactic =>
  `(tactic| exact boundary_ne_program $outside (inProgram_of_textOffset $offset (by decide)))

def loadBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0xbc, 0x24, 0x8f, 0, 0, 0,
   0x4c, 0x8b, 0xac, 0x24, 0xb0, 0, 0, 0,
   0x4c, 0x89, 0xfb, 0x48, 0x83, 0xf3, 0x3f]

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f95a
  tailLength : MemReadable s (rspOf s + 143) 1
  blocks : MemReadable s (rspOf s + 176) 8

def loadLength (s : RamState) : BitVec 64 :=
  (memLoad s.external (rspOf s + 143) 8).setWidth 64

def loadEffect (s : RamState) : Effect :=
  { rip := 0x10f972
    writes := [⟨(.reg 15 : Operand 64), loadLength s⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 176) 64⟩,
      ⟨(.reg 3 : Operand 64), loadLength s ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem load_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10f95a loadBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xf95a loadBytes
    (by decide +kernel) (by decide +kernel)

theorem load_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x10f95a loadBytes) (Effect.post loadEffect) := by
  advance_begin (show StepEffect _ _ (movzxR32M8Effect 0x10f95a 9 15
    (.sib 4 none 0 (.d32 143))) from
    movzx_r_m8_rex_effect_step _ 0x44 (by simp [RexPrefix]) 32
      (.inr rfl) (fun _ => rfl) 7 (.sib 4 none 0 (.d32 143)) (by decide) rfl rfl)
  case pre =>
    intro s hp
    exact ⟨hp.rip, hp.tailLength⟩
  case next => intro s hp; internal outside 0xf963
  advance_then (mov_r64_m64_effect_step 0x10f963 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f95a loadBytes 9 8
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, ?_⟩
    · x86_norm
      exact hp.blocks
    · internal outside 0xf96b
  advance_then (mov_r64_r64_effect_step 0x10f96b 0x4c 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f95a loadBytes 17 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf96e⟩
  advance_then (StepEffect.forgetFlags (h :=
    xor_r64_imm8_effect_step 0x10f96e 0x48 0xf3 63 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10f95a loadBytes 20 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf972⟩
  advance_finish [loadEffect, loadLength]

def markerAddress (s : RamState) : BitVec 64 :=
  rspOf s + ((.reg 15 : Operand 64).read s + 80)

structure MarkPre (s : RamState) : Prop where
  rip : s.RIP = 0x10f972
  writable : MemWritable s (markerAddress s) 1
  codeApart : RangeApart (markerAddress s) 1 0x10f972 19

def markBytes : List UInt8 :=
  [0x42, 0xc6, 0x44, 0x3c, 0x50, 0x80, 0x4a, 0x8d, 0x3c, 0x3c,
   0x48, 0x83, 0xc7, 0x51, 0x31, 0xf6, 0x48, 0x89, 0xda]

def markEffect (s : RamState) : Effect :=
  { rip := 0x10f985
    writes := [⟨(.mem (markerAddress s) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + ((.reg 15 : Operand 64).read s + 81)⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem mark_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10f972 markBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xf972 markBytes
    (by decide +kernel) (by decide +kernel)

attribute [local x86_compose] movM8Imm8RexEffect addR64Imm8Effect
  BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

theorem mark_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary MarkPre (codeRange 0x10f972 markBytes) (Effect.post markEffect) := by
  advance_begin (mov_m8_imm8_rex_effect_step 0x10f972 0x42 (by simp [RexPrefix])
    (.sib 4 (some 15) 0 (.d8 80)) (by decide) rfl rfl 128)
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_, ?_⟩
    · x86_norm
      exact hp.writable
    · intro i hi j hj
      x86_norm
      simpa only [x86_compose, markerAddress, rspOf, BitVec.add_assoc] using
        hp.codeApart i hi j (by change j < 6 at hj; omega)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.codeApart
  case next => intro s hp; internal outside 0xf978
  advance_then (lea_r64_effect_step 0x10f978 0x4a (by simp [RexWPrefix]) 7
    (.sib 4 (some 15) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f972 markBytes 6 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf97c⟩
  advance_then (StepEffect.forgetFlags (h :=
    add_r64_imm8_effect_step 0x10f97c 0x48 0xc7 81 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10f972 markBytes 10 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf980⟩
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect 0x10f980 2 6 6) from
      xor_r32_r32_effect_step 0x10f980 0xf6 rfl)))
  case sub => exact codeRange_slice_subset 0x10f972 markBytes 14 2
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf982⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10f982 2 3) from
    mov_r64_r64_effect_step 0x10f982 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f972 markBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid, by internal outside 0xf985⟩
  advance_finish [markEffect, markerAddress]

theorem branch_run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x10f98b) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .rbx).toNat < 8 then 0x10f995 else 0x10f320) ∧
      AgreesExcept [.flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, run, readyU, compared⟩ :=
    (cmp_r64_imm8_effect_step 0x10f98b 0x48 0xfb 7 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice code 0xf98b [0x48, 0x83, 0xfb, 0x07]
        (by decide) (by decide +kernel)) rip
      (by internal outside 0xf98f)
  have frame : AgreesExcept [.flags, .rip] s u := compared.agrees
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step 0x10f98f 7 0xfffff98b u readyU
    (programText_slice (frame.codeIn (by simp [Component.Covers]) code)
      0xf98f [0x0f, 0x87, 0x8b, 0xf9, 0xff, 0xff] (by decide) (by decide +kernel))
    ⟨compared.rip, fun _ => by decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = (s.regValue .rbx).ult 7 :=
    compared.flags.1
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rbx - 7 == 0) :=
    compared.flags.2.2.2.1
  have target : t.RIP = (if (s.regValue .rbx).toNat < 8 then 0x10f995 else 0x10f320) := by
    rw [jumped.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then (0x10f320 : BitVec 64) else 0x10f995) = _
    rw [carry, zero]
    have zeroEq : (s.regValue .rbx - 7 == 0) = decide ((s.regValue .rbx).toNat = 7) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · exact congrArg BitVec.toNat
      · intro h
        apply BitVec.eq_of_toNat_eq
        exact h
    rw [zeroEq]
    have condition : (!((s.regValue .rbx).ult 7 || decide ((s.regValue .rbx).toNat = 7))) =
        decide (8 ≤ (s.regValue .rbx).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [condition]
    by_cases small : (s.regValue .rbx).toNat < 8
    · simp only [small, show ¬8 ≤ (s.regValue .rbx).toNat by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    · simp only [small, show 8 ≤ (s.regValue .rbx).toNat by omega, decide_true, ↓reduceIte]
  have advance : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [target]
    split
    · internal outside 0xf995
    · internal outside 0xf320))
  have jumpFrame : AgreesExcept [.rip] u t := jumped.agrees
  exact ⟨t, run.trans advance, readyT, target, (frame.trans jumpFrame).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding
