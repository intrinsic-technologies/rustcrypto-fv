import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Store

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Instructions

def bytes : List UInt8 := [0x44,0x88,0xa4,0x24,0xef,0x00,0,0]

def effect (s : RamState) : Effect :=
  { rip := 0x102838
    writes := [⟨(.mem (rspOf s + 239) : Operand 8), (Operand.reg 12 : Operand 8).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x102830 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x2830 bytes (by decide) (by decide +kernel)

theorem step [Bindings] :
    StepEffect (StorePre 0x102830 8 (fun s => rspOf s + 239) 1)
      (codeRange 0x102830 bytes) effect :=
  mov_m8_r8_effect_step 0x102830 0x44 (by simp [RexPrefix]) 4
    (.sib 4 none 0 (.d32 239)) (by decide) rfl rfl

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : StorePre 0x102830 8 (fun s => rspOf s + 239) 1 s)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ (effect s).Holds s t :=
  step.advances ready (code loaded) pre
    (boundary_ne_program outside (inProgram_of_textOffset 0x2838 (by decide)))

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Store
