import Hkdf.Proofs.Common.SHA256.Frame
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Compose
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

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.ShiftLeft

structure EndPointerPre (s : RamState) : Prop where
  rip : s.RIP = 0x1095da
  writable : Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 200) 8
  apart : RangeApart (stackPtr s + 200) 8 0x1095da 18

def endPointerBytes : List UInt8 :=
  [0x48,0x89,0xd0,0x48,0xc1,0xe0,6,0x48,1,0xf0,0x48,0x89,0x84,0x24,0xc8,0,0,0]

def endPointerEffect (s : RamState) : Effect :=
  { rip := 0x1095ec
    writes := [⟨(Operand.reg 0 : Operand 64), (s.regValue .rdx <<< 6) + s.regValue .rsi⟩,
      ⟨(Operand.mem (stackPtr s + 200) : Operand 64), (s.regValue .rdx <<< 6) + s.regValue .rsi⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

attribute [local x86_compose] shlR64Effect shlFlags

set_option maxHeartbeats 800000 in
theorem end_pointer_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary EndPointerPre (codeRange 0x1095da endPointerBytes)
      (Effect.post endPointerEffect) := by
  advance_begin mov_r64_r64_effect_step 0x1095da 0x48 0xd0 (by simp [RexWPrefix]) rfl
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x95dd (by decide))
  advance_then shl_r64_imm8_effect_step 0x1095dd 0x48 0xe0 6 (by simp [RexWPrefix]) rfl rfl
  case loc => exact shlR64Effect_local _ _ _ 6 (by decide)
  case sub => exact codeRange_slice_subset 0x1095da endPointerBytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, shlR64Effect_components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x95e1 (by decide))⟩
  advance_then add_r64_r64_effect_step 0x1095e1 0x48 0xf0 (by simp [RexWPrefix]) rfl
  case sub => exact codeRange_slice_subset 0x1095da endPointerBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x95e4 (by decide))⟩
  advance_then Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x1095e4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl
  case sub => exact codeRange_slice_subset 0x1095da endPointerBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (10 + j) (by omega)
      change stackPtr s + (200 : BitVec 64) + BitVec.ofNat 64 i =
        (0x1095e4 : BitVec 64) + BitVec.ofNat 64 j at he
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · x86_norm
      exact boundary_ne_program outside (inProgram_of_textOffset 0x95ec (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [endPointerEffect]
  · x86_norm [endPointerEffect]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [endPointerEffect]
  · x86_norm [endPointerEffect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end Hkdf.Proofs.Common.SHA256
