import P256.Proofs.Verifying.Wrapper.ReturnState
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure SuccessStorePre (s : RamState) : Prop where
  rip : s.RIP = 0x103216
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .r12) 8
  codeApart : RangeApart (s.regValue .r12) 8 0x103216 10

def successStoreBytes : List UInt8 := [73, 199, 4, 36, 0, 0, 0, 0, 49, 192]

def successStoreEffect (s : RamState) : Effect :=
  { rip := 0x103220
    writes := [⟨(.mem (s.regValue .r12) : Operand 64), 0⟩,
      ⟨(.reg 0 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem success_store [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SuccessStorePre (codeRange 0x103216 successStoreBytes)
      (Effect.post successStoreEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
    0x103216 0x49 (by simp [RexWPrefix]) (.sib 12 none 0 .none) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s
        (s.regValue .r12 + 0#64) 8
      exact (congrArg (fun x => P256.Proofs.Common.Instructions.CrossPageStore.Writable s x 8)
        (BitVec.add_zero (s.regValue .r12))).mpr h.writable
    · change RangeApart (s.regValue .r12 + 0#64) 8 0x103216 8
      rw [BitVec.add_zero]
      intro i hi j hj he
      exact h.codeApart i hi j (by omega) he
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x321e (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [State.regValue, Operand.read_reg64, gprNumber]
    change RangeApart (s.regValue .r12 + 0#64) 8 0x103216 10
    rw [BitVec.add_zero]
    exact h.codeApart
  advance_then (xor_r32_r32_effect_step 0x10321e 0xc0 (by decide))
  case sub => exact codeRange_slice_subset 0x103216 successStoreBytes 8 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3220 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [successStoreEffect]
  · x86_norm [successStoreEffect, Operand.read_reg64, State.regValue, gprNumber,
      rexR, rexB, modrmRm, modrmReg]
    constructor
    · exact (BitVec.add_zero (s.regValue .r12)).symm
    · change (0 : BitVec 64) = ((s.regValue .rax).setWidth 32 ^^^ (s.regValue .rax).setWidth 32).setWidth 64
      rw [BitVec.xor_self]
      rfl
  · intro f
    cases f <;> x86_norm [successStoreEffect, xorFlags, gprNumber, modrmRm, modrmReg]
    · change evenParity (BitVec.extractLsb' 0 8 (0 : BitVec 32)) =
        evenParity (BitVec.extractLsb' 0 8
          (((Operand.reg 0 : Operand 32).read s) ^^^ (Operand.reg 0 : Operand 32).read s))
      rw [BitVec.xor_self]
      rfl
    · change true = ((((Operand.reg 0 : Operand 32).read s) ^^^
        (Operand.reg 0 : Operand 32).read s) == (0 : BitVec 32))
      rw [BitVec.xor_self]
      rfl
    · change (0 : BitVec 32).msb =
        (((Operand.reg 0 : Operand 32).read s) ^^^ (Operand.reg 0 : Operand 32).read s).msb
      rw [BitVec.xor_self]
      rfl
  · x86_norm [successStoreEffect, Operand.read_reg64, State.regValue, gprNumber,
      rexR, rexB, modrmRm, modrmReg]
    exact BitVec.add_zero (s.regValue .r12)

end P256.Proofs.Verifying.Wrapper
