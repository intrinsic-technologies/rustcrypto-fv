import P256.Proofs.Sec1.Affine.Uncompressed.Curve.CopyX
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.CopyY
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Frame
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copyY_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x1109fa) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (copyYEffect t).Holds t u := by
  have hp : CopyYPre t := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · intro off member
      apply ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre state (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    · intro off member
      apply ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state (by decide) _ (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    · intro off member pc len bound
      apply ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state (by decide) _ bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copyY_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x109fa copyYBytes
      (by decide +kernel) (by decide +kernel)) hp
  refine ⟨fuel, u, run, after_stack pre state ready effect.agrees ?_, effect⟩
  refine ⟨?_, by simp [copyYEffect, Effect.components],
    by simp [copyYEffect, Effect.components], by simp [copyYEffect, Effect.components],
    by simp [copyYEffect, Effect.components]⟩
  intro address len member
  simp only [copyYEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨16, rfl, by decide⟩
  · exact ⟨24, rfl, by decide⟩
  · exact ⟨32, rfl, by decide⟩
  · exact ⟨40, rfl, by decide⟩

theorem copyY_value {s t : RamState} {x : Nat}
    (value : MontgomeryAt s (stackPtr s + 448) x)
    (effect : (copyYEffect s).Holds s t)
    (allocated : MemReadable t (stackPtr s + 16) 32) :
    MontgomeryAt t (stackPtr s + 16) x := by
  apply montgomeryAt_of_memLoad_limbs value.1 allocated.mem
  intro j hj
  have input := value.memLoad_limb j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at input ⊢
  · exact effect.writes.1.trans input
  · exact effect.writes.2.1.trans input
  · exact effect.writes.2.2.1.trans input
  · exact effect.writes.2.2.2.1.trans input

theorem copyX_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110a46) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (copyXEffect t).Holds t u := by
  have hp : CopyXPre t := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · intro off member
      apply ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre state (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    · intro off member
      apply ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state (by decide) _ (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    · intro off member pc len bound
      apply ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state (by decide) _ bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copyX_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10a46 copyXBytes
      (by decide +kernel) (by decide +kernel)) hp
  refine ⟨fuel, u, run, after_stack pre state ready effect.agrees ?_, effect⟩
  refine ⟨?_, by simp [copyXEffect, Effect.components],
    by simp [copyXEffect, Effect.components], by simp [copyXEffect, Effect.components],
    by simp [copyXEffect, Effect.components]⟩
  intro address len member
  simp only [copyXEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨16, rfl, by decide⟩
  · exact ⟨24, rfl, by decide⟩
  · exact ⟨32, rfl, by decide⟩
  · exact ⟨40, rfl, by decide⟩

theorem copyX_value {s t : RamState} {x : Nat}
    (value : MontgomeryAt s (stackPtr s + 480) x)
    (effect : (copyXEffect s).Holds s t)
    (allocated : MemReadable t (stackPtr s + 16) 32) :
    MontgomeryAt t (stackPtr s + 16) x := by
  apply montgomeryAt_of_memLoad_limbs value.1 allocated.mem
  intro j hj
  have input := value.memLoad_limb j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at input ⊢
  · exact effect.writes.1.trans input
  · exact effect.writes.2.1.trans input
  · exact effect.writes.2.2.1.trans input
  · exact effect.writes.2.2.2.1.trans input

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
