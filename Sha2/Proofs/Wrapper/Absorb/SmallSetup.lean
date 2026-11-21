import Sha2.Proofs.Common.EffectCompose.AddImmediate
import Sha2.Proofs.Common.Field.Operations.Run.Compose
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.SmallSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes : List UInt8 :=
  [0x4a,0x8d,0x3c,0x24,0x48,0x81,0xc7,0xc0,0x0,0x0,0x0,0x4c,0x89,0xee,0x48,0x89,0xda]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0xb1)
    writes := [⟨(.reg 7 : Operand 64), rspOf s + ((Operand.reg 12 : Operand 64).read s) + 192⟩,
      ⟨(.reg 6 : Operand 64), ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), ((Operand.reg 3 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s + ((Operand.reg 12 : Operand 64).read s)) 192).2) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xa0) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xa0) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0xa0))
      (codeRange (v.pc 0xa0) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (lea_r64_effect_step (v.pc 0xa0) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    change v.pc 0xa0 + BitVec.ofNat 64 4 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xa4 < 1024))
  advance_then (add_r64_imm32_effect_step (v.pc 0xa4) 0x48 0xc7 192 (by simp [RexWPrefix]) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0xa0 4]
    exact codeRange_slice_subset (v.pc 0xa0) bytes 4 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xa4 + BitVec.ofNat 64 7 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xab < 1024))⟩
  advance_then (mov_r64_r64_effect_step (v.pc 0xab) 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0xa0 11]
    exact codeRange_slice_subset (v.pc 0xa0) bytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xab + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xae < 1024))⟩
  advance_then (mov_r64_r64_effect_step (v.pc 0xae) 0x48 0xda (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0xa0 14]
    exact codeRange_slice_subset (v.pc 0xa0) bytes 14 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xae + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xb1 < 1024))⟩
  advance_finish [Variant.pc_add, effect, BitVec.add_zero, BitVec.shiftLeft_zero]

end Sha2.Proofs.Wrapper.Absorb.SmallSetup
