import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.Instructions.ShiftLeft.Word32Rex
import Sha2.Proofs.Common.Instructions.Bswap
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
import Sha2.Proofs.Common.Instructions.Or

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Padding.Length

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.Or (orR64R64Effect or_r64_r64_effect_step)
open Sha2.Proofs.Common.Instructions.ShiftLeft

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64

@[local x86_local] theorem shift64_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (shlR64Effect p n r c s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, shlR64Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, shlR64Effect, Write.Full, Operand.Full]

@[local x86_local] theorem shift32_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (shlR32Effect p n r c s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, shlR32Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, shlR32Effect, Write.Full, Operand.Full]

def bytes : List UInt8 :=
  [0x49, 0xc1, 0xe4, 0x9, 0x41, 0xc1, 0xe7, 0x3, 0x4d, 0x9, 0xe7, 0x49, 0xf, 0xcf]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x2c2)
    writes := [⟨(.reg 12 : Operand 64), (.reg 12 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 15 : Operand 64), bswap64
        (((.reg 15 : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg 12 : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x2b4) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x2b4) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x2b4))
      (codeRange (v.pc 0x2b4) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR64Effect (v.pc 0x2b4) 4 12 9) from
      shl_r64_imm8_effect_step (v.pc 0x2b4) 0x49 0xe4 9 (by simp [RexWPrefix]) rfl rfl)))
  case next =>
    intro _ _
    change v.pc 0x2b4 + BitVec.ofNat 64 4 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x2b8 < 1024))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR32Effect (v.pc 0x2b8) 4 15 3) from
      shl_r32_imm8_rex_effect_step (v.pc 0x2b8) 0x41 0xe7 3 (by simp [RexNoWPrefix]) rfl rfl)))
  case sub =>
    rw [← Variant.pc_add v 0x2b4 4]
    exact codeRange_slice_subset (v.pc 0x2b4) bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, shlR32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · change v.pc 0x2b8 + BitVec.ofNat 64 4 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x2bc < 1024))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (orR64R64Effect (v.pc 0x2bc) 15 12) from
      or_r64_r64_effect_step (v.pc 0x2bc) 0x4d 0xe7 (by simp [RexWPrefix]) rfl)))
  case sub =>
    rw [← Variant.pc_add v 0x2b4 8]
    exact codeRange_slice_subset (v.pc 0x2b4) bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · change v.pc 0x2bc + BitVec.ofNat 64 3 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x2bf < 1024))
  advance_then (bswap_r64_effect_step (v.pc 0x2bf) 15)
  case sub =>
    rw [← Variant.pc_add v 0x2b4 11]
    exact codeRange_slice_subset (v.pc 0x2b4) bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · change v.pc 0x2bf + BitVec.ofNat 64 3 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x2c2 < 1024))
  advance_finish [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, effect]

end Sha2.Proofs.Wrapper.Hash.Padding.Length
