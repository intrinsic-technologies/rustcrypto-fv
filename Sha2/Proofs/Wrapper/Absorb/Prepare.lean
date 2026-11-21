import Sha2.Proofs.Common.EffectCompose.Memory
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

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Prepare

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes : List UInt8 :=
  [0xba,0x40,0,0,0,0x4c,0x29,0xe2,0x48,0x89,0xdd,0x48,0x29,0xd5]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0xfc)
    writes := [⟨(.reg 2 : Operand 64), 64 - s.regValue .r12⟩,
      ⟨(.reg 5 : Operand 64), s.regValue .rbx - (64 - s.regValue .r12)⟩]
    flags := some (.ofStatusFlags (subSpec (s.regValue .rbx) (64 - s.regValue .r12)).2) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xee) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xee) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0xee))
      (codeRange (v.pc 0xee) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (mov_r32_imm32_effect_step (v.pc 0xee) 0xba (by decide +kernel) 64)
  case next =>
    intro _ _
    change v.pc 0xee + BitVec.ofNat 64 5 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xf3 < 1024))
  advance_then (sub_r64_r64_effect_step (v.pc 0xf3) 0x4c 0xe2 (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0xee 5]
    exact codeRange_slice_subset (v.pc 0xee) bytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xf3 + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xf6 < 1024))⟩
  advance_then (mov_r64_r64_effect_step (v.pc 0xf6) 0x48 0xdd (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0xee 8]
    exact codeRange_slice_subset (v.pc 0xee) bytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xf6 + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xf9 < 1024))⟩
  advance_then (sub_r64_r64_effect_step (v.pc 0xf9) 0x48 0xd5 (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0xee 11]
    exact codeRange_slice_subset (v.pc 0xee) bytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xf9 + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xfc < 1024))⟩
  advance_finish [Variant.pc_add, effect]

end Sha2.Proofs.Wrapper.Absorb.Prepare
