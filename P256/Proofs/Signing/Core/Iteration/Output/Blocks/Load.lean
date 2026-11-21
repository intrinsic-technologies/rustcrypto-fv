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

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d33e
  readable : ∀ off ∈ ([536, 544] : List Nat), MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8

def LoadBytes : List UInt8 :=
  [76, 139, 164, 36, 24, 2, 0, 0, 72, 139, 156, 36, 32, 2, 0, 0]

def LoadEffect (s : RamState) : Effect :=
  { rip := 0x10d34e
    writes := [⟨(.reg 12 : Operand 64), (Operand.mem (stackPtr s + 536) : Operand 64).read s⟩,
      ⟨(.reg 3 : Operand 64), (Operand.mem (stackPtr s + 544) : Operand 64).read s⟩] }

set_option maxHeartbeats 1000000 in
theorem Load_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x10d33e LoadBytes) (Effect.post LoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d33e 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 536)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable 536 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd346 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d346 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 544)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d33e LoadBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 544 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd34e (by decide))
  advance_finish [LoadEffect, stackPtr, Operand.read_reg64, State.regValue, gprNumber]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks
