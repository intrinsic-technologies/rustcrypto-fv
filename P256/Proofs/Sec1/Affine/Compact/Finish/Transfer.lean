import P256.Proofs.Sec1.Affine.Compact.Finish.X
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem transfer_x [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110500)
    (input : Field.MontgomeryAt t (stackPtr s - 480) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110540 ∧
      Field.MontgomeryAt u (stackPtr s - 120) value ∧
      (xEffect t).Holds t u := by
  have hp : XPre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro off member
      have bound : off+8 ≤ 760 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) bound
    · intro off member
      have bound : off+8 ≤ 760 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      exact ScalarFrame.stack_writable pre.toCalleePre state (by decide) bound (by decide)
    · intro off member pc len bound
      have ho : off+8 ≤ 760 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      exact ScalarFrame.stack_code pre.toCalleePre state (by decide) ho bound
  obtain ⟨n,u,run,ready,_,effect⟩ := x_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10500 xBytes
      (by decide) (by decide +kernel)) hp
  have writes : Uncompressed.Curve.StackWrites t (xEffect t).components := by
    constructor
    · intro address count member
      simp only [xEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨640,rfl,by decide⟩
      · exact ⟨648,rfl,by decide⟩
      · exact ⟨656,rfl,by decide⟩
      · exact ⟨664,rfl,by decide⟩
    all_goals simp [xEffect,Effect.components]
  have frame := Uncompressed.Curve.after_stack pre state ready effect.agrees writes
  have source : stackPtr t + 280 = stackPtr s - 480 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have destination : stackPtr t + 640 = stackPtr s - 120 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  refine ⟨n,u,run,frame,effect.rip,?_,effect⟩
  rw [← destination]
  apply Uncompressed.Output.montgomery_words (source := stackPtr t+280)
  · rwa [source]
  · exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)
  · exact readable_of_grow
      (ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)) effect.agrees.grow
  · intro j hj
    have values := effect.writes
    simp only [xEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.2.1

end P256.Proofs.Sec1.Affine.Compact.Finish
