import P256.Proofs.Signing.Core.Iteration.Stages
import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output.Blocks

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Common.Field

structure RetryPre (s : RamState) : Prop where
  rip : s.RIP = 0x10caa0

def RetryBytes : List UInt8 :=
  [72, 141, 92, 36, 40]

def RetryEffect (s : RamState) : Effect :=
  { rip := 0x10caa5
    writes := [⟨(.reg 3 : Operand 64), stackPtr s + 40⟩] }

set_option maxHeartbeats 1000000 in
theorem Retry_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary RetryPre (codeRange 0x10caa0 RetryBytes) (Effect.post RetryEffect) := by
  advance_begin (lea_r64_effect_step 0x10caa0 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xcaa5 (by decide))
  advance_finish [RetryEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks
