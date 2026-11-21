import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
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
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def cursorAddress (s : RamState) : BitVec 64 :=
  (Operand.mem (s.regValue .rsi) : Operand 64).read s

def pointAddress (s : RamState) : BitVec 64 :=
  (Operand.mem (cursorAddress s) : Operand 64).read s

structure CursorPre (s : RamState) : Prop where
  rip : s.RIP = 0x10b17a
  wrapper : MemReadable s (s.regValue .rsi) 8
  cursor : Writable s (cursorAddress s) 8
  apart : RangeApart (cursorAddress s) 8 0x10b17a 19

def cursorBytes : List UInt8 :=
  [0x48,0x89,0xfb,0x48,0x8b,0x06,0x48,0x8b,0x08,0x48,0x8d,0x91,0x80,0,0,0,
    0x48,0x89,0x10]

def cursorEffect (s : RamState) : Effect :=
  { rip := 0x10b18d
    writes := [⟨(Operand.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(Operand.reg 0 : Operand 64), cursorAddress s⟩,
      ⟨(Operand.reg 1 : Operand 64), pointAddress s⟩,
      ⟨(Operand.reg 2 : Operand 64), pointAddress s + 128⟩,
      ⟨(Operand.mem (cursorAddress s) : Operand 64), pointAddress s + 128⟩] }

theorem cursor_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CursorPre (codeRange 0x10b17a cursorBytes)
      (Effect.post cursorEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10b17a 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xb17d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10b17d 0x48 (by simp [RexWPrefix]) 0
    (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10b17a cursorBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb180 (by decide))⟩
    x86_norm [BitVec.add_zero]
    exact hP.wrapper
  advance_then (mov_r64_m64_effect_step 0x10b180 0x48 (by simp [RexWPrefix]) 1
    (.base 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10b17a cursorBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb183 (by decide))⟩
    x86_norm [BitVec.add_zero]
    exact hP.cursor.toMemReadable
  advance_then (lea_r64_effect_step 0x10b183 0x48 (by simp [RexWPrefix]) 2
    (.base 1 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10b17a cursorBytes 9 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xb18a (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10b18a 0x48 (by simp [RexWPrefix]) 2 (.base 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10b17a cursorBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds
      hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simp only [BitVec.add_zero]
      exact hP.cursor
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (16 + j) (by omega)
      simp only [BitVec.add_zero] at he
      change cursorAddress s + BitVec.ofNat 64 i = 0x10b18a + BitVec.ofNat 64 j at he
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [BitVec.add_zero]
      exact hP.apart
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xb18d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [cursorEffect, cursorAddress, pointAddress, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [cursorEffect, cursorAddress, pointAddress, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [cursorEffect, cursorAddress, pointAddress, BitVec.add_zero]
  · x86_norm [cursorEffect, cursorAddress, pointAddress, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
