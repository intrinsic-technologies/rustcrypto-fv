import P256.Proofs.Sec1.Affine.Uncompressed.Curve.OutputX
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.OutputY
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Constants

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outputX_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110b5a) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (outputXEffect t).Holds t u := by
  have hp : OutputXPre t := by
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
  obtain ⟨fuel, u, run, ready, _, effect⟩ := outputX_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10b5a outputXBytes
      (by decide +kernel) (by decide +kernel)) hp
  refine ⟨fuel, u, run, after_stack pre state ready effect.agrees ?_, effect⟩
  refine ⟨?_, by simp [outputXEffect, Effect.components],
    by simp [outputXEffect, Effect.components], by simp [outputXEffect, Effect.components],
    by simp [outputXEffect, Effect.components]⟩
  intro address len member
  simp only [outputXEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨512, rfl, by decide⟩
  · exact ⟨520, rfl, by decide⟩
  · exact ⟨528, rfl, by decide⟩
  · exact ⟨536, rfl, by decide⟩

theorem outputX_value {s t : RamState} {x : Nat}
    (value : MontgomeryAt s (stackPtr s + 480) x)
    (effect : (outputXEffect s).Holds s t)
    (allocated : MemReadable t (stackPtr s + 512) 32) :
    MontgomeryAt t (stackPtr s + 512) x := by
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

theorem outputY_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110b9a) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (outputYEffect t).Holds t u := by
  have hp : OutputYPre t := by
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
  obtain ⟨fuel, u, run, ready, _, effect⟩ := outputY_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10b9a outputYBytes
      (by decide +kernel) (by decide +kernel)) hp
  refine ⟨fuel, u, run, after_stack pre state ready effect.agrees ?_, effect⟩
  refine ⟨?_, by simp [outputYEffect, Effect.components],
    by simp [outputYEffect, Effect.components], by simp [outputYEffect, Effect.components],
    by simp [outputYEffect, Effect.components]⟩
  intro address len member
  simp only [outputYEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false, Component.mem.injEq, reduceCtorEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨544, rfl, by decide⟩
  · exact ⟨552, rfl, by decide⟩
  · exact ⟨560, rfl, by decide⟩
  · exact ⟨568, rfl, by decide⟩

theorem outputY_value {s t : RamState} {x : Nat}
    (value : MontgomeryAt s (stackPtr s + 448) x)
    (effect : (outputYEffect s).Holds s t)
    (allocated : MemReadable t (stackPtr s + 544) 32) :
    MontgomeryAt t (stackPtr s + 544) x := by
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

def outputComponents (s : RamState) (offset : Nat) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s-BitVec.ofNat 64 offset) 32]

theorem output_byte {s t u : RamState} {dest offset len : Nat}
    (h : AgreesExcept (outputComponents s dest) t u)
    (apart : OffsetsApart (-BitVec.ofNat 64 dest) 32 (-BitVec.ofNat 64 offset) len)
    (bound : 32+len < 2^64) {i : Nat} (hi : i < len) :
    u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc ha
  simp only [outputComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j,hj,he⟩ := ha
  apply OffsetsApart.ne apart (stackPtr s) hj hi bound
  simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem outputX_frame [Bindings] {s t u : RamState} (state : Frame s t)
    (effect : (outputXEffect t).Holds t u) :
    AgreesExcept (outputComponents s 248) t u := by
  apply P256.Proofs.Sec1.Decompress.Cubic.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [outputXEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [outputComponents]
  · intro c hc a ha
    simp only [outputXEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s-248) 32, by simp [outputComponents], ?_⟩
      rw [state.rsp]
    · refine ⟨0+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨8+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨16+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨24+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]

theorem outputY_frame [Bindings] {s t u : RamState} (state : Frame s t)
    (effect : (outputYEffect t).Holds t u) :
    AgreesExcept (outputComponents s 216) t u := by
  apply P256.Proofs.Sec1.Decompress.Cubic.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [outputYEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [outputComponents]
  · intro c hc a ha
    simp only [outputYEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s-216) 32, by simp [outputComponents], ?_⟩
      rw [state.rsp]
    · refine ⟨0+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨8+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨16+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    · refine ⟨24+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
