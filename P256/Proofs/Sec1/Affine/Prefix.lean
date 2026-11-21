import P256.Proofs.Sec1.Affine.Prologue
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions.Lea32
open P256.Proofs.Common.Encoding.Parser.CompressedRoute

structure PrefixPre (s : RamState) : Prop where
  rip : s.RIP = 0x1100e1
  input : MemReadable s (s.regValue .rsi) 1

def prefixBytes : List UInt8 :=
  [0x48, 0x89, 0xfb, 0x0f, 0xb6, 0x06, 0x0f, 0xb6, 0xc8,
   0x8d, 0x51, 0xfe, 0x83, 0xfa, 0x04]

def prefixEffect (s : RamState) : Effect :=
  let tag := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 8).read s
  let index := tag.setWidth 32 - 2
  { rip := 0x1100f0
    writes := [⟨(.reg 3 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), tag.setWidth 64⟩,
      ⟨(.reg 1 : Operand 64), tag.setWidth 64⟩,
      ⟨(.reg 2 : Operand 64), index.setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec index 4)) }

attribute [local x86_compose] movzxAlEffect leaR32Effect

private theorem movzxAl_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (movzxAlEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movzxAlEffect, h.read_reg]
  · intro s
    simp [movzxAlEffect, Write.Full, Operand.Full]

private theorem leaIndex_local :
    Effect.Local (leaR32Effect 0x1100ea 2 (.base 1 (.d8 0xfe)) 3) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [leaR32Effect, AddrMode.addr, AddrMode.reg64, h.read_reg]
  · intro s
    simp [leaR32Effect, Write.Full, Operand.Full]

attribute [local x86_local] movzxAl_local leaIndex_local

private theorem index_width (tag : BitVec 8) :
    ((tag.setWidth 64 + 18446744073709551614).setWidth 32) = tag.setWidth 32 - 2 := by
  revert tag
  decide +kernel

set_option maxHeartbeats 800000 in
theorem prefix_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary PrefixPre (codeRange 0x1100e1 prefixBytes) prefixEffect := by
  unfold prefixBytes
  slice_run_begin (show StepEffect _ _ (movR64R64Effect 0x1100e1 3 7) from
    mov_r64_r64_effect_step 0x1100e1 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x100e4 (by decide))
  slice_run_then (show StepEffect _ _ (movzxR32M8Effect 0x1100e4 3 0 (.base 6 .none)) from
    movzx_r32_m8_effect_step 0x1100e4 0 (.base 6 .none) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1100e1) 3 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x100e7 (by decide))
  slice_run_then (show StepEffect _ _ (movzxAlEffect 0x1100e7 1) from
    movzx_r32_al_effect_step 0x1100e7 0xc8 rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1100e1) 6 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x100ea (by decide))
  slice_run_then (show StepEffect _ _ (leaR32Effect 0x1100ea 2 (.base 1 (.d8 0xfe)) 3) from
    lea_r32_legacy_effect_step 0x1100ea 2 (.base 1 (.d8 0xfe)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1100e1) 9 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x100ed (by decide))
  slice_run_then (show StepEffect _ _ (cmpR32Imm8Effect 0x1100ed 3 2 4) from
    cmp_r32_imm8_effect_step 0x1100ed 0xfa 4 rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x1100e1) 12 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x100f0 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect]
    simp only [BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq]
    exact ⟨trivial, trivial, congrArg (BitVec.setWidth 64) (index_width _).symm⟩
  · intro f; cases f <;> x86_norm [prefixEffect]
    all_goals simp only [BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    · exact congrArg StatusFlags.CF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
    · exact congrArg StatusFlags.PF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
    · exact congrArg StatusFlags.AF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
    · exact congrArg StatusFlags.ZF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
    · exact congrArg StatusFlags.SF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
    · exact congrArg StatusFlags.OF (congrArg (fun x : BitVec 32 => cmpSpec x 4) (index_width _).symm)
  · x86_norm [prefixEffect]

end P256.Proofs.Sec1.Affine
