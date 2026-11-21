import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StorePre (s : RamState) : Prop where
  rip : s.RIP = 0x112ebe
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 0 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 →
      RangeApart ((Operand.reg 0 : Operand 64).read s + i) 8
        (Extracted.textAddress + BitVec.ofNat 64 offset) len

def storeBytes : List UInt8 :=
  [0x48, 0x89, 0x08, 0x48, 0x89, 0x50, 0x08,
    0x48, 0x89, 0x78, 0x10, 0x48, 0x89, 0x70, 0x18]

def storeEffect (s : RamState) : Effect :=
  { rip := 0x112ecd
    writes := [
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s) : Operand 64),
        (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s + 8) : Operand 64),
        (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s + 16) : Operand 64),
        (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s + 24) : Operand 64),
        (Operand.reg 6 : Operand 64).read s⟩] }

theorem store_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StorePre (codeRange 0x112ebe storeBytes)
      (Effect.post storeEffect) := by
  refine AdvanceTriple.block_first ?k (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112ebe 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 0 .none)
    (by decide +kernel) rfl rfl) ?sub ?pre ?av ?next
  case' k => x86_norm
  case sub => exact codeRange_slice_subset 0x112ebe storeBytes 0 3
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · exact h.writable 0 (by simp)
    · exact h.codeApart 0 (by simp) 0x12ebe 3 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 0 (by simp) 0x12ebe 15 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12ec1 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112ec1 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 0 (.d8 8))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ebe storeBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x12ec1 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x12ebe 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ec5 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112ec5 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.base 0 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ebe storeBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x12ec5 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x12ebe 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ec9 (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x112ec9 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 0 (.d8 24))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112ebe storeBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x12ec9 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x12ebe 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12ecd (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [storeEffect]
  · x86_norm [storeEffect]
    simp [gprNumber, rexR]
  · intro i
    cases i <;> x86_norm [storeEffect]
  · x86_norm [storeEffect]
    simp

end P256.Proofs.Projective.Multiply.Machine.Radix.Serialize
