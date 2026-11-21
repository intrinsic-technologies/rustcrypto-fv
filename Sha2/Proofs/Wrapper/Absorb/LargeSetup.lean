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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.LargeSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x0,0x1,0x0,0x0,0x4c,0x89,0xee]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x168)
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 256⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r13⟩] }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x15d) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x15d) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x15d))
      (codeRange (v.pc 0x15d) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (lea_r64_effect_step (v.pc 0x15d) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    change v.pc 0x15d + BitVec.ofNat 64 8 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x165 < 1024))
  advance_then (mov_r64_r64_effect_step (v.pc 0x165) 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub =>
    rw [← Variant.pc_add v 0x15d 8]
    exact codeRange_slice_subset (v.pc 0x15d) bytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by simp only [Variant.pc_add]), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0x165 + BitVec.ofNat 64 3 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x168 < 1024))⟩
  advance_finish [Variant.pc_add, effect, BitVec.add_zero]

end Sha2.Proofs.Wrapper.Absorb.LargeSetup
