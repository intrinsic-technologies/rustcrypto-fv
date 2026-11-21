import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
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

namespace Sha2.Proofs.Wrapper.Absorb.Blocks.TailRegisters

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

attribute [local x86_compose] andR32Imm8Effect

@[local x86_local] theorem and32_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (andR32Imm8Effect p len dst imm) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andR32Imm8Effect, h.read_reg]
  · intro s
    simp [andR32Imm8Effect, Write.Full, Operand.Full]

def bytes : List UInt8 :=
  [0x48,0x89,0xe8,0x48,0xb9,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,
   0x48,0x21,0xc8,0x83,0xe5,0x3f,0x49,0x01,0xc5]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x183)
    writes := [⟨(.reg 0 : Operand 64), 0x7fffffffffffffc0 &&& s.regValue .rbp⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 5 : Operand 64), ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .r13 + (0x7fffffffffffffc0 &&& s.regValue .rbp)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxHeartbeats 800000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x16d))
      (codeRange (v.pc 0x16d) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (mov_r64_r64_effect_step (v.pc 0x16d) 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s hs
    change v.pc 0x16d + BitVec.ofNat 64 3 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide))
  advance_then (mov_r64_imm64_effect_step (v.pc 0x170) 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub =>
    rw [← Variant.pc_add v 0x16d 3]
    exact codeRange_slice_subset (v.pc 0x16d) bytes 3 10
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by
        change v.pc 0x170 + BitVec.ofNat 64 10 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))⟩
  advance_then (and_r64_r64_effect_step (v.pc 0x17a) 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0x16d 13]
    exact codeRange_slice_subset (v.pc 0x16d) bytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by
        change v.pc 0x17a + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))⟩
  advance_then (and_r32_imm8_effect_step (v.pc 0x17d) 0xe5 63 rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x16d 16]
    exact codeRange_slice_subset (v.pc 0x16d) bytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by
        change v.pc 0x17d + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))⟩
  advance_then (add_r64_r64_effect_step (v.pc 0x180) 0x49 0xc5 (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0x16d 19]
    exact codeRange_slice_subset (v.pc 0x16d) bytes 19 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      (by
        change v.pc 0x180 + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide)))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect, Variant.pc_add, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effect, Variant.pc_add, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [effect, Variant.pc_add]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

end Sha2.Proofs.Wrapper.Absorb.Blocks.TailRegisters
