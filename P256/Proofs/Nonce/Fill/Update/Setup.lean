import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Update.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

def bytes : List UInt8 := [0xbe, 8, 0, 0, 0, 0x31, 0xd2]

def effect (s : RamState) : Effect :=
  { rip := 0x1073e6
    writes := [⟨(.reg 6 : Operand 64), 8⟩, ⟨(.reg 2 : Operand 64), BitVec.setWidth 64
      ((Operand.reg 2 : Operand 32).read s ^^^ (Operand.reg 2 : Operand 32).read s)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1073df bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x73df bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1073df)
      (codeRange 0x1073df bytes) (Effect.post effect) := by
  advance_begin (mov_r32_imm32_effect_step 0x1073df 0xbe (by decide) 8)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x73e4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags
    (h := xor_r32_r32_effect_step 0x1073e4 0xd2 rfl))
  case sub => exact codeRange_slice_subset 0x1073df bytes 5 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by change ∀ c : Component, c ∈ [.reg 2, .flags, .rip] → ∀ a, ¬ c.Covers a; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x73e6 (by decide))⟩
  advance_finish [effect]

end P256.Proofs.Nonce.Fill.Update.Setup
