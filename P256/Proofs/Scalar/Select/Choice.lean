import P256.Proofs.Scalar.Select.Prefix
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
set_option autoImplicit false
namespace P256.Proofs.Scalar.Select
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

def choiceBytes : List UInt8 := [0x88,0x0c,0x24,0x48,0x89,0xe1,0x0f,0xb6,0x0c,0x24]
def choiceEffect (s : RamState) : Effect :=
  { rip := 0x113280
    writes := [⟨(.reg 1 : Operand 64), ((.reg 1 : Operand 8).read s).setWidth 64⟩,
      ⟨(.mem (stackPtr s) : Operand 8), (.reg 1 : Operand 8).read s⟩] }
structure ChoicePre (s : RamState) : Prop where
  rip : s.RIP = 0x113276
  writable : MemWritable s (stackPtr s) 1
  apart : RangeApart (stackPtr s) 1 0x113276 10

set_option maxHeartbeats 600000 in
theorem choice_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ChoicePre (codeRange 0x113276 choiceBytes) (Effect.post choiceEffect) := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x113276 1 (by decide) (.sib 4 none 0 .none) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 0#64) 1
      simpa only [BitVec.add_zero] using h.writable
    · change RangeApart (stackPtr s + 0#64) 1 0x113276 3
      rw [BitVec.add_zero]
      exact fun i hi j hj => h.apart i hi j (by omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simp only [BitVec.add_zero]
    exact h.apart
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x13279 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113279 0x48 0xe1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113276 choiceBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1327c (by decide))⟩
  advance_then (movzx_r32_m8_effect_step 0x11327c 1 (.sib 4 none 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113276 choiceBytes 6 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13280 (by decide))⟩
    x86_norm
    simp only [BitVec.add_zero]
    exact ⟨hP.writable.low, hP.writable.mem⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [choiceEffect]
  · x86_norm [choiceEffect, stackPtr, BitVec.add_zero]
    exact ⟨Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
  · intro i; cases i <;> x86_norm [choiceEffect]
  · x86_norm [choiceEffect, stackPtr, BitVec.add_zero]
    rfl
end P256.Proofs.Scalar.Select
