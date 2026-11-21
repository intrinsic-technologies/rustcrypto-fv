import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Wrapper.Hash.Padding.StoreByte
import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Common.EffectCompose.Advance
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
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Padding.FillSetup

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

attribute [local x86_compose] movM8Imm8RexEffect incR64Effect BitVec.shiftLeft_zero BitVec.add_zero BitVec.xor_self BitVec.setWidth_zero

@[local x86_local] theorem byteStore_local (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8RexEffect p am imm) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8RexEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8RexEffect, storeEffect, Write.Full, Operand.Full]

@[local x86_local] theorem increment_local (p : BitVec 64) (r : BitVec 5) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (incR64Effect p r s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, incR64Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, incR64Effect, Write.Full, Operand.Full]

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0x1e5)
  writable : MemWritable s (rspOf s + (Operand.reg 15 : Operand 64).read s) 1
  codeApart : RangeApart (rspOf s + (Operand.reg 15 : Operand 64).read s) 1 (v.pc 0x1e5) 17

def bytes : List UInt8 :=
  [0x42, 0xc6, 0x4, 0x3c, 0x80, 0x4a, 0x8d, 0x3c, 0x3c, 0x48, 0xff, 0xc7, 0x31, 0xf6, 0x48, 0x89, 0xda]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x1f6)
    writes := [⟨(.mem (rspOf s + (Operand.reg 15 : Operand 64).read s) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg 15 : Operand 64).read s + 1⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x1e5) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x1e5) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x1e5) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (mov_m8_imm8_rex_effect_step (v.pc 0x1e5) 0x42 (by simp [RexNoWPrefix])
    (.sib 4 (some 15) 0 .none) (by cases v <;> decide) rfl rfl 128)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      exact h.writable
    · x86_norm
      intro i hi j hj
      exact h.codeApart i hi j (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart
  case next =>
    intro _ _
    change v.pc 0x1e5 + BitVec.ofNat 64 5 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1ea < 1024))
  advance_then (show StepEffect _ _ (leaR64Effect (v.pc 0x1ea) 7 (.sib 4 (some 15) 0 .none)) from
    lea_r64_effect_step (v.pc 0x1ea) 0x4a (by simp [RexWPrefix]) 7
      (.sib 4 (some 15) 0 .none) (by cases v <;> decide) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x1e5 5]
    exact codeRange_slice_subset (v.pc 0x1e5) bytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · change v.pc 0x1ea + BitVec.ofNat 64 4 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1ee < 1024))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (incR64Effect (v.pc 0x1ee) 7) from
      inc_r64_effect_step (v.pc 0x1ee) 0x48 0xc7 (by simp [RexWPrefix]) rfl rfl)))
  case sub =>
    rw [← Variant.pc_add v 0x1e5 9]
    exact codeRange_slice_subset (v.pc 0x1e5) bytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, incR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · change v.pc 0x1ee + BitVec.ofNat 64 3 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1f1 < 1024))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR32R32Effect (v.pc 0x1f1) 2 6 6) from
      xor_r32_r32_effect_step (v.pc 0x1f1) 0xf6 rfl)))
  case sub =>
    rw [← Variant.pc_add v 0x1e5 12]
    exact codeRange_slice_subset (v.pc 0x1e5) bytes 12 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, xorR32R32Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · change v.pc 0x1f1 + BitVec.ofNat 64 2 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1f3 < 1024))
  advance_then (show StepEffect _ _ (movR64R64Effect (v.pc 0x1f3) 2 3) from
    mov_r64_r64_effect_step (v.pc 0x1f3) 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0x1e5 14]
    exact codeRange_slice_subset (v.pc 0x1e5) bytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · change v.pc 0x1f3 + BitVec.ofNat 64 3 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1f6 < 1024))
  advance_finish [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, effect]

end Sha2.Proofs.Wrapper.Hash.Padding.FillSetup
