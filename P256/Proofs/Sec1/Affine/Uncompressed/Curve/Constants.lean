import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Preserve
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Model
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.StoreA
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.StoreB
import P256.Proofs.Sec1.Decompress.Cubic.Support

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratchComponents (s : RamState) : List Component :=
  [.reg 0, .rip, .mem (stackPtr s-744) 32]

theorem scratch_byte {s t u : RamState} (h : AgreesExcept (scratchComponents s) t u)
    {offset len : Nat}
    (apart : OffsetsApart (-(744 : BitVec 64)) 32 (-BitVec.ofNat 64 offset) len)
    (bound : 32+len < 2^64) {i : Nat} (hi : i < len) :
    u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc ha
  simp only [scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j,hj,he⟩ := ha
  apply OffsetsApart.ne apart (stackPtr s) hj hi bound
  simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem PreservesInputs.of_scratch {s t u : RamState}
    (h : AgreesExcept (scratchComponents s) t u) : PreservesInputs s t u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.read (n := 64) (r := 3) (by simp [scratchComponents])
    · exact h.read (n := 64) (r := 15) (by simp [scratchComponents])
  · intro w hw i hi
    simp only [preservedWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    all_goals exact scratch_byte h (by unfold OffsetsApart; decide +kernel) (by decide) hi

theorem store_a_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110aa8) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110ad8 ∧
      MontgomeryAt u (stackPtr s-744) P256.Spec.Operations.domain.a ∧
      AgreesExcept (scratchComponents s) t u := by
  have hp : APre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro off member
      have bound : off.toNat + 8 ≤ 760 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state (by decide) bound (by decide)
    · intro off member pc len bound
      have upper : off.toNat + 8 ≤ 760 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state (by decide) upper bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := store_a boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10aa8 aBytes
      (by decide +kernel) (by decide +kernel)) hp
  have frame : Frame s u := by
    apply after_stack pre state ready effect.agrees
    refine ⟨?_, by simp [aEffect, Effect.components], by simp [aEffect, Effect.components],
      by simp [aEffect, Effect.components], by simp [aEffect, Effect.components]⟩
    intro address len member
    simp only [aEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
      or_false, false_or, Nat.reduceDiv, Component.mem.injEq, reduceCtorEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨40, rfl, by decide⟩
    · exact ⟨24, rfl, by decide⟩
    · exact ⟨32, rfl, by decide⟩
    · exact ⟨16, rfl, by decide⟩
  have coarse : AgreesExcept (scratchComponents s) t u := by
    apply P256.Proofs.Sec1.Decompress.Cubic.agrees_of_footprint effect.agrees
    · intro c hc hm
      simp only [aEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try simp [Component.isMem] at hm
      all_goals simp [scratchComponents]
    · intro c hc a ha
      simp only [aEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals
        obtain ⟨i, hi, rfl⟩ := ha
        refine ⟨.mem (stackPtr s-744) 32, by simp [scratchComponents], ?_⟩
        rw [state.rsp]
      · refine ⟨24+i, by omega, ?_⟩
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
      · refine ⟨0+i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have address : stackPtr t+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 16) state.rsp (by decide) (by decide)
  have allocated : MemReadable u (stackPtr t+16) 32 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre frame
      (offset := 16) (len := 32) (by decide) (by decide)
    simpa only [frame.rsp, state.rsp, BitVec.ofNat_eq_ofNat] using h
  have value : MontgomeryAt u (stackPtr t+16) P256.Spec.Operations.domain.a := by
    apply coefficient_a allocated.mem
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd]
    · exact effect.writes.2.2.2.2
    · exact effect.writes.2.2.1
    · exact effect.writes.2.2.2.1
    · exact effect.writes.2.1
  rw [address] at value
  exact ⟨fuel, u, run, frame, effect.rip, value, coarse⟩

theorem store_b_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110b06) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110b42 ∧
      MontgomeryAt u (stackPtr s-744) P256.Spec.Operations.domain.b ∧
      AgreesExcept (scratchComponents s) t u := by
  have hp : BPre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro off member
      have bound : off.toNat + 8 ≤ 760 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state (by decide) bound (by decide)
    · intro off member pc len bound
      have upper : off.toNat + 8 ≤ 760 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state (by decide) upper bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := store_b boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10b06 bBytes
      (by decide +kernel) (by decide +kernel)) hp
  have frame : Frame s u := by
    apply after_stack pre state ready effect.agrees
    refine ⟨?_, by simp [bEffect, Effect.components], by simp [bEffect, Effect.components],
      by simp [bEffect, Effect.components], by simp [bEffect, Effect.components]⟩
    intro address len member
    simp only [bEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
      or_false, false_or, Nat.reduceDiv, Component.mem.injEq, reduceCtorEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨40, rfl, by decide⟩
    · exact ⟨32, rfl, by decide⟩
    · exact ⟨24, rfl, by decide⟩
    · exact ⟨16, rfl, by decide⟩
  have coarse : AgreesExcept (scratchComponents s) t u := by
    apply P256.Proofs.Sec1.Decompress.Cubic.agrees_of_footprint effect.agrees
    · intro c hc hm
      simp only [bEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try simp [Component.isMem] at hm
      all_goals simp [scratchComponents]
    · intro c hc a ha
      simp only [bEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals
        obtain ⟨i, hi, rfl⟩ := ha
        refine ⟨.mem (stackPtr s-744) 32, by simp [scratchComponents], ?_⟩
        rw [state.rsp]
      · refine ⟨24+i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
      · refine ⟨16+i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
      · refine ⟨8+i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
      · refine ⟨0+i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        simp only [← BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have address : stackPtr t+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 16) state.rsp (by decide) (by decide)
  have allocated : MemReadable u (stackPtr t+16) 32 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre frame
      (offset := 16) (len := 32) (by decide) (by decide)
    simpa only [frame.rsp, state.rsp, BitVec.ofNat_eq_ofNat] using h
  have value : MontgomeryAt u (stackPtr t+16) P256.Spec.Operations.domain.b := by
    apply montgomeryAt_coefficient_b allocated.mem
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd]
    · exact effect.writes.2.2.2.2
    · exact effect.writes.2.2.2.1
    · exact effect.writes.2.2.1
    · exact effect.writes.2.1
  rw [address] at value
  exact ⟨fuel, u, run, frame, effect.rip, value, coarse⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
