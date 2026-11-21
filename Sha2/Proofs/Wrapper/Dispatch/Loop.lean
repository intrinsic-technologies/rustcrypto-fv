import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.EffectCompose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper.Variant
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
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Dispatch.Loop

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes : List UInt8 := [0x49,0x89,0xf7,0x45,0x31,0xf6,0xeb,0x37]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := v.pc 0xcd
    writes := [⟨(.reg 15 : Operand 64), (.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 14 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x8e) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x8e) bytes
  · cases v <;> decide
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc 0x8e) (codeRange (v.pc 0x8e) bytes)
      (Effect.post (fun s => effect s v)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect (v.pc 0x8e) 15 6) from
    mov_r64_r64_effect_step (v.pc 0x8e) 0x49 0xf7
      (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (by
    have h := Variant.pc_inProgram v (by cases v <;> decide : 0x91 < 1024)
    simpa [movR64R64Effect, Variant.pc_add] using h)
  advance_then (show StepEffect _ _ (xorR32R32Effect (v.pc 0x91) 3 14 14) from
    xor_r32_r32_rex_effect_step (v.pc 0x91) 0x45 0xf6
      (by simp [RexNoWPrefix]) rfl)
  case sub =>
    have hpc : v.pc 0x8e + BitVec.ofNat 64 3 = v.pc 0x91 := by
      simpa only [show 0x8e + 3 = 0x91 by decide] using Variant.pc_add v 0x8e 3
    rw [← hpc]
    exact codeRange_slice_subset (v.pc 0x8e) bytes 3 3
  case mid =>
    intro s t _ hH _
    have hpc : v.pc 0x8e + BitVec.ofNat 64 3 = v.pc 0x91 := by
      simpa only [show 0x8e + 3 = 0x91 by decide] using Variant.pc_add v 0x8e 3
    refine ⟨hH.rip.trans hpc, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (by
      have h := Variant.pc_inProgram v (by cases v <;> decide : 0x94 < 1024)
      simpa [xorR32R32Effect, Variant.pc_add] using h)
  advance_then (show StepEffect _ _ (fun _ => nopEffect (v.pc 0xcd) 0) from
    have htarget : branchTarget (v.pc 0x94) 2 ((0x37 : BitVec 8).signExtend 64) =
        v.pc 0xcd := by
      cases v <;> decide
    have hjump : (fun _ : RamState => jmpEffect (v.pc 0x94) 2 ((0x37 : BitVec 8).signExtend 64)) =
        (fun _ => nopEffect (v.pc 0xcd) 0) := by
      funext s
      simp only [jmpEffect, nopEffect]
      rw [htarget]
      simp
    hjump ▸ jmp_rel8_effect_step (v.pc 0x94) 0x37 (by
      have h := congrArg BitVec.toNat htarget
      rw [h]
      cases v <;> decide))
  case sub =>
    have hpc : v.pc 0x8e + BitVec.ofNat 64 6 = v.pc 0x94 := by
      simpa only [show 0x8e + 6 = 0x94 by decide] using Variant.pc_add v 0x8e 6
    rw [← hpc]
    exact codeRange_slice_subset (v.pc 0x8e) bytes 6 2
  case mid =>
    intro s t _ hH _
    have hpc : v.pc 0x91 + BitVec.ofNat 64 3 = v.pc 0x94 := by
      simpa only [show 0x91 + 3 = 0x94 by decide] using Variant.pc_add v 0x91 3
    refine ⟨hH.rip.trans hpc, Effect.Avoids.of_noMem
      (by simp [nopEffect, Effect.components, Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (by
      have h := Variant.pc_inProgram v (by cases v <;> decide : 0xcd < 1024)
      simpa [nopEffect] using h)
  advance_finish [effect, nopEffect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.add_zero]

end Sha2.Proofs.Wrapper.Dispatch.Loop
