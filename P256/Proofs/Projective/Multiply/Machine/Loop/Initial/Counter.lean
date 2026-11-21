import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import P256.Proofs.Common.Instructions.ShiftLeft.Compose
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.ShiftLeft (shlFlags shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step shlR64Effect_local)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem initial_nop_local (p : BitVec 64) (len : Nat) :
    Effect.Local (fun _ : RamState => nopEffect p len) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t ho
    rfl
  · intro t
    simp [nopEffect]

attribute [local x86_compose] shlR64Effect shlFlags nopEffect nopMemLen

structure CounterPre (s : RamState) : Prop where
  rip : s.RIP = 0x103290
  writable0 : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s) 8
  apart0 : RangeApart (stackPtr s) 8 0x103290 32

def counterBytes : List UInt8 :=
  [72,137,208,72,193,224,6,72,1,208,72,137,4,36,69,49,237,73,137,223,
    102,102,102,46,15,31,132,0,0,0,0,0]

def counterEffect (s : RamState) : Effect :=
  { rip := 0x1032b0
    writes := [⟨(Operand.reg 0 : Operand 64), (s.regValue .rdx <<< 6) + s.regValue .rdx⟩,
      ⟨(Operand.mem (stackPtr s) : Operand 64), (s.regValue .rdx <<< 6) + s.regValue .rdx⟩,
      ⟨(Operand.reg 13 : Operand 64), 0⟩,
      ⟨(Operand.reg 15 : Operand 64), s.regValue .rbx⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem counter_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CounterPre (codeRange 0x103290 counterBytes) (Effect.post counterEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x103290 0x48 0xd0 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x3293 (by decide))
  advance_then (shl_r64_imm8_effect_step 0x103293 0x48 0xe0 6 (by simp [RexWPrefix]) rfl rfl)
  case loc => exact shlR64Effect_local _ _ _ 6 (by decide)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, shlR64Effect_components]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3297 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x103297 0x48 0xd0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x329a (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10329a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + (0 : BitVec 64)) 8
      simpa using hP.writable0
    · x86_norm
      intro i hi j hj he
      apply hP.apart0 i hi (10 + j) (by omega)
      change stackPtr s + (0 : BitVec 64) + BitVec.ofNat 64 i = _ at he
      simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (stackPtr s + (0 : BitVec 64)) 8 0x103290 32
      simpa using hP.apart0
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x329e (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x10329e 0x45 0xed
    (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 14 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32a1 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1032a1 0x49 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 17 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32a4 (by decide))⟩
  advance_then (nop_m_effect_step 0x1032a4 [0x66,0x66,0x66,0x2e]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103290 counterBytes 20 12
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers, nopEffect, Effect.components]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x32b0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [counterEffect, BitVec.add_zero, BitVec.xor_self]
  · x86_norm [counterEffect, BitVec.add_zero, BitVec.xor_self]
    refine ⟨rfl, rfl, ?_, rfl⟩
    change (0 : BitVec 64) = (((s.regValue .r13).setWidth 32 ^^^ (s.regValue .r13).setWidth 32).setWidth 64)
    simp
  · intro i; cases i <;> x86_norm [counterEffect, BitVec.add_zero, BitVec.xor_self]
  · x86_norm [counterEffect, BitVec.add_zero, BitVec.xor_self]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
