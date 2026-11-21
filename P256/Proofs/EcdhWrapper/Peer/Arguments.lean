import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def argumentBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0x78,0x01,0,0,0x48,0x8d,0xb4,0x24,0xf0,0,0,0]

def argumentEffect (s : RamState) : Effect :=
  { rip := 0x106b80
    writes := [⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s+376⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s+240⟩] }

theorem arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x106b70)
      (codeRange 0x106b70 argumentBytes) (Effect.post argumentEffect) := by
  advance_begin (lea_r64_effect_step 0x106b70 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6b78 (by decide))
  advance_then (lea_r64_effect_step 0x106b78 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106b70 argumentBytes 8 8
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x6b80 (by decide))⟩
  advance_finish [argumentEffect]

end P256.Proofs.EcdhWrapper.Peer
