import P256.Proofs.Scalar.Select.Epilogue
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Memory.Readable
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
set_option autoImplicit false
namespace P256.Proofs.Scalar.Select
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
attribute [local x86_compose] subR64Imm8Effect stackPtr

def prefixBytes : List UInt8 := [0x48,0x83,0xec,1,0x48,0x89,0xf8,0x48,0x8b,0x3e,0x4c,0x8b,0x46,8,0x4c,0x8b,0x4e,16,0x48,0x8b,0x76,24]
def prefixEffect (s : RamState) : Effect :=
  { rip := 0x113276
    writes := [⟨(.reg 4 : Operand 64), stackPtr s - 1⟩,
      ⟨(.reg 0 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 7 : Operand 64), (.mem (s.regValue .rsi) : Operand 64).read s⟩,
      ⟨(.reg 8 : Operand 64), (.mem (s.regValue .rsi+8) : Operand 64).read s⟩,
      ⟨(.reg 9 : Operand 64), (.mem (s.regValue .rsi+16) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (.mem (s.regValue .rsi+24) : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (subSpec (stackPtr s) (1 : BitVec 64)).2) }

set_option maxHeartbeats 800000 in
theorem prefix_correct [Bindings] (boundary : ReturnBoundary) :
    AdvanceTriple boundary (fun s => CalleePre s boundary 0x113260 32 32 16)
      (codeRange 0x113260 prefixBytes) (Effect.post prefixEffect) := by
  advance_begin (sub_r64_imm8_effect_step 0x113260 0x48 0xec 1 (by simp [RexWPrefix]) rfl rfl)
  case next => exact fun _ h => boundary_ne_program h.outerBoundary (inProgram_of_textOffset 0x13264 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113264 0x48 0xf8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113260 prefixBytes 4 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x13267 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x113267 0x48 (by simp [RexWPrefix]) 7 (.base 6 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113260 prefixBytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x1326a (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub
      (memoryRegion_memReadable hP.inputBounded hP.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) 0 8 (by change _ ≤ 32; decide)
  advance_then (mov_r64_m64_effect_step 0x11326a 0x4c (by simp [RexWPrefix]) 0 (.base 6 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113260 prefixBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x1326e (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub
      (memoryRegion_memReadable hP.inputBounded hP.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) 8 8 (by change _ ≤ 32; decide)
  advance_then (mov_r64_m64_effect_step 0x11326e 0x4c (by simp [RexWPrefix]) 1 (.base 6 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113260 prefixBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x13272 (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub
      (memoryRegion_memReadable hP.inputBounded hP.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) 16 8 (by change _ ≤ 32; decide)
  advance_then (mov_r64_m64_effect_step 0x113272 0x48 (by simp [RexWPrefix]) 6 (.base 6 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113260 prefixBytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x13276 (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub
      (memoryRegion_memReadable hP.inputBounded hP.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) 24 8 (by change _ ≤ 32; decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect, BitVec.add_zero]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [prefixEffect] <;> rfl
  · x86_norm [prefixEffect]
end P256.Proofs.Scalar.Select
