import P256.Proofs.Common.Scalar.Addition.Output.Choice.Prefix
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Run
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.ByteLogic

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def choiceByte (t : RamState) : BitVec 8 :=
  (if t.regValue .r12 = 0 then 1 else 0) &&& (t.regValue .r13).setWidth 8

namespace Choice

def prefixBytes : List UInt8 :=
  [0x48,0x89,0xf8,0x4d,0x85,0xe4,0x0f,0x94,0xc1,0x44,0x20,0xe9]

def prefixEffect (s : RamState) : Effect :=
  { rip := 0x113a4e
    writes := [⟨(Operand.reg 0 : Operand 64), s.regValue .rdi⟩,
      ⟨(Operand.reg 1 : Operand 64), mergeGPR 8 (choiceByte s) (s.regValue .rcx)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

set_option maxHeartbeats 800000 in
theorem prefix_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113a42)
      (codeRange 0x113a42 prefixBytes) (Effect.post prefixEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113a42 0x48 0xf8 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13a45 (by decide))
  advance_then (test_r64_r64_effect_step 0x113a45 0x4d 0xe4 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113a42 prefixBytes 3 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip, by x86_avoid, boundary_ne_program hout (inProgram_of_textOffset 0x13a48 (by decide))⟩
  advance_then_on [.ZF] using (setcc_r8_effect_step 0x113a48 0x94 0xc1 (.inr rfl) rfl (by decide))
  case sub => exact codeRange_slice_subset 0x113a42 prefixBytes 6 3
  case mid =>
    intro s t hp hh ho hf
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program hout (inProgram_of_textOffset 0x13a4b (by decide))⟩
  advance_then (and_r8_r8_rex_effect_step 0x113a4b 0x44 0xe9 (by simp [RexPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113a42 prefixBytes 9 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program hout (inProgram_of_textOffset 0x13a4e (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect,choiceByte,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,
      gprNumber, rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec_ofNat,
      BitVec.reduceExtractLsb', BitVec.reduceToNat, BitVec.and_self, testFlags]
    constructor
    · rfl
    · exact (P256.Proofs.Common.Scalar.Addition.Choice.merge_byte_twice _ _ _).symm
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [prefixEffect]

end Choice
end P256.Proofs.Signing.Core.Iteration.Components.Addition
