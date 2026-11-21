import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs


structure LookupSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10338e
  readable : MemReadable s (stackPtr s + 8) 8
  digit : MemReadable s ((Operand.mem (stackPtr s + 8) : Operand 64).read s + s.regValue .rbx) 1

def lookupSetupBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x08,0x0f,0xb6,0x14,0x18,0x4c,0x89,0xe7,0x4c,0x89,0xfe]

def lookupSetupEffect (s : RamState) : Effect :=
  { rip := 0x10339d
    writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (stackPtr s + 8) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), ((Operand.mem
        ((Operand.mem (stackPtr s + 8) : Operand 64).read s + s.regValue .rbx) : Operand 8).read s).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64), s.regValue .r12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r15⟩] }

theorem lookup_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LookupSetupPre (codeRange 0x10338e lookupSetupBytes)
      (Effect.post lookupSetupEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10338e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x3393 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x103393 2 (.sib 0 (some 3) 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10338e lookupSetupBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3397 (by decide))⟩
    x86_norm
    simp only [BitVec.shiftLeft_zero, BitVec.add_zero]
    exact hP.digit
  advance_then (mov_r64_r64_effect_step 0x103397 0x4c 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10338e lookupSetupBytes 9 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x339a (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10339a 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10338e lookupSetupBytes 12 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x339d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lookupSetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [lookupSetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [lookupSetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [lookupSetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
