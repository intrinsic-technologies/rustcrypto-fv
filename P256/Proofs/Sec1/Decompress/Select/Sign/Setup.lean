import P256.Proofs.Sec1.Decompress.Select.Parity.Model
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Common.Instructions.ByteLogic.Unary
import P256.Proofs.Common.Instructions.ByteLogic.XorLoad
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Sec1.Decompress.Cubic.Support

set_option autoImplicit false
open P256.Proofs.Sec1.Decompress.Cubic (input_stack_address)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.ByteLogic (notAlEffect not_al_effect_step xorR8M8LegacyEffect xor_al_rsp4c_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_effect_step)
open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.Decompress.Select.Sign
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def setupBytes : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x20,0x0f,0xb6,0xc8,0x4c,0x89,0xee,0x4c,0x89,0xe2]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x11005a
    writes := [⟨(.reg 7 : Operand 64),stackPtr s+32⟩,
      ⟨(.reg 1 : Operand 64),((Operand.reg 0 : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(Operand.reg 12 : Operand 64).read s⟩] }

theorem setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x11004c)
      (codeRange 0x11004c setupBytes) (Effect.post setupEffect) := by
  have h1 : (0x110051 : BitVec 64) ≠ boundary.rip :=
    boundary_ne_program hout (inProgram_of_textOffset 0x10051 (by decide))
  have h2 : (0x110054 : BitVec 64) ≠ boundary.rip :=
    boundary_ne_program hout (inProgram_of_textOffset 0x10054 (by decide))
  have h3 : (0x110057 : BitVec 64) ≠ boundary.rip :=
    boundary_ne_program hout (inProgram_of_textOffset 0x10057 (by decide))
  have h4 : (0x11005a : BitVec 64) ≠ boundary.rip :=
    boundary_ne_program hout (inProgram_of_textOffset 0x1005a (by decide))
  have step1 : StepEffect (fun s => s.RIP=0x11004c)
      (codeRange 0x11004c [0x48,0x8d,0x7c,0x24,0x20])
      (leaR64Effect 0x11004c 7 (.sib 4 none 0 (.d8 32))) :=
    lea_r64_effect_step 0x11004c 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid]) rfl rfl
  have step2 : StepEffect (fun s => s.RIP=0x110051)
      (codeRange 0x110051 [0x0f,0xb6,0xc8]) (movzxR32R8Effect 0x110051 3 1 0) :=
    movzx_r32_r8_effect_step 0x110051 0xc8 rfl (by decide)
  have step3 : StepEffect (fun s => s.RIP=0x110054)
      (codeRange 0x110054 [0x4c,0x89,0xee]) (movR64R64Effect 0x110054 6 13) :=
    mov_r64_r64_effect_step 0x110054 0x4c 0xee (by simp [RexWPrefix]) (by decide)
  have step4 : StepEffect (fun s => s.RIP=0x110057)
      (codeRange 0x110057 [0x4c,0x89,0xe2]) (movR64R64Effect 0x110057 2 12) :=
    mov_r64_r64_effect_step 0x110057 0x4c 0xe2 (by simp [RexWPrefix]) (by decide)
  advance_begin step1
  advance_then step2
  advance_then step3
  advance_then step4
  advance_finish [setupEffect]
  all_goals first
    | exact codeRange_slice_subset 0x11004c setupBytes 5 3
    | exact codeRange_slice_subset 0x11004c setupBytes 8 3
    | exact codeRange_slice_subset 0x11004c setupBytes 11 3
    | (repeat constructor <;> rfl)


end P256.Proofs.Sec1.Decompress.Select.Sign
