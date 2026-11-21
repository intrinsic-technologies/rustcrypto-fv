import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.Instructions.XorImmediate
import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Common.EffectCompose.Memory
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Padding.LoadSetup

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.XorImmediate

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0x1ce)
  tailLength : MemReadable s (rspOf s + 63) 1
  blocks : MemReadable s (rspOf s + 96) 8

def bytes : List UInt8 :=
  [0x4c, 0x8d, 0x74, 0x24, 0x40, 0x44, 0xf, 0xb6, 0x7c, 0x24, 0x3f, 0x4c, 0x8b, 0x64, 0x24, 0x60, 0x4c, 0x89, 0xfb, 0x48, 0x83, 0xf3, 0x3f]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x1e5)
    writes := [⟨(.reg 14 : Operand 64), rspOf s + 64⟩,
      ⟨(.reg 15 : Operand 64), (memLoad s.external (rspOf s + 63) 8).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + 96) 64⟩,
      ⟨(.reg 3 : Operand 64), (memLoad s.external (rspOf s + 63) 8).setWidth 64 ^^^ 63⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x1ce) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x1ce) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x1ce) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (show StepEffect _ _ (leaR64Effect (v.pc 0x1ce) 14 (.sib 4 none 0 (.d8 64))) from lea_r64_effect_step (v.pc 0x1ce) 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 64)) (by cases v <;> decide) rfl rfl)
  case next =>
    intro _ _
    change v.pc 0x1ce + BitVec.ofNat 64 5 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1d3 < 1024))
  advance_then (show StepEffect _ _ (movzxR32M8Effect (v.pc 0x1d3) 6 15 (.sib 4 none 0 (.d8 63))) from
    movzx_r_m8_rex_effect_step (v.pc 0x1d3) 0x44 (by simp [RexPrefix]) 32 (.inr rfl)
      (fun _ => rfl) 7 (.sib 4 none 0 (.d8 63)) (by cases v <;> decide) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x1ce 5]
    exact codeRange_slice_subset (v.pc 0x1ce) bytes 5 6
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      exact hP.tailLength
    · simp [Component.Covers]
    · change v.pc 0x1d3 + BitVec.ofNat 64 6 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1d9 < 1024))
  advance_then (show StepEffect _ _ (movR64M64Effect (v.pc 0x1d9) 12 (.sib 4 none 0 (.d8 96))) from
    mov_r64_m64_effect_step (v.pc 0x1d9) 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d8 96)) (by cases v <;> decide) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0x1ce 11]
    exact codeRange_slice_subset (v.pc 0x1ce) bytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      exact hP.blocks
    · simp [Component.Covers]
    · change v.pc 0x1d9 + BitVec.ofNat 64 5 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1de < 1024))
  advance_then (show StepEffect _ _ (movR64R64Effect (v.pc 0x1de) 3 15) from
    mov_r64_r64_effect_step (v.pc 0x1de) 0x4c 0xfb (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0x1ce 16]
    exact codeRange_slice_subset (v.pc 0x1ce) bytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · change v.pc 0x1de + BitVec.ofNat 64 3 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1e1 < 1024))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (xorR64Imm8Effect (v.pc 0x1e1) 3 63) from
      xor_r64_imm8_effect_step (v.pc 0x1e1) 0x48 0xf3 63 (by simp [RexWPrefix]) rfl rfl)))
  case sub =>
    rw [← Variant.pc_add v 0x1ce 19]
    exact codeRange_slice_subset (v.pc 0x1ce) bytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, xorR64Imm8Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · change v.pc 0x1e1 + BitVec.ofNat 64 4 ≠ boundary.rip
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x1e5 < 1024))
  advance_finish [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, effect]

end Sha2.Proofs.Wrapper.Hash.Padding.LoadSetup
