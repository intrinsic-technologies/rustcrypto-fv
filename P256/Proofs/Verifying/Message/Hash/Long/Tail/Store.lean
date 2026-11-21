import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail.Store

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Instructions

def bytes : List UInt8 := [0x40,0x88,0xac,0x24,0x17,0x2,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10d6ec
    writes := [⟨(.mem (rspOf s + 535) : Operand 8), (Operand.reg 5 : Operand 8).read s⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d6e4 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd6e4 bytes (by decide) (by decide +kernel)

theorem step [Bindings] :
    StepEffect (StorePre 0x10d6e4 8 (fun s => rspOf s + 535) 1)
      (codeRange 0x10d6e4 bytes) effect :=
  mov_m8_r8_effect_step 0x10d6e4 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d32 535)) (by decide) rfl rfl

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : StorePre 0x10d6e4 8 (fun s => rspOf s + 535) 1 s)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ (effect s).Holds s t :=
  step.advances ready (code loaded) pre
    (boundary_ne_program outside (inProgram_of_textOffset 0xd6ec (by decide)))

end P256.Proofs.Verifying.Message.Hash.Long.Tail.Store
