import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Sec1.Affine.Compact.Copy.Y
import P256.Proofs.Sec1.Affine.Compact.Copy.X
import P256.Proofs.Sec1.Affine.Compact.Copy.NegateY
import P256.Proofs.Sec1.Affine.Compact.Copy.NegateX

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem transfer_y [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110294)
    (input : Field.MontgomeryAt t (stackPtr s - 448) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1102d4 ∧
      Field.MontgomeryAt u (stackPtr s - 632) value ∧
      (yEffect t).Holds t u := by
  have hp : YPre t := by
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
  obtain ⟨n,u,run,ready,_,effect⟩ := y_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10294 yBytes
      (by decide) (by decide +kernel)) hp
  have writes : Uncompressed.Curve.StackWrites t (yEffect t).components := by
    constructor
    · intro address count member
      simp only [yEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨128,rfl,by decide⟩
      · exact ⟨136,rfl,by decide⟩
      · exact ⟨144,rfl,by decide⟩
      · exact ⟨152,rfl,by decide⟩
    all_goals simp [yEffect,Effect.components]
  have frame := Uncompressed.Curve.after_stack pre state ready effect.agrees writes
  have source : stackPtr t + 312 = stackPtr s - 448 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have destination : stackPtr t + 128 = stackPtr s - 632 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  refine ⟨n,u,run,frame,effect.rip,?_,effect⟩
  rw [← destination]
  apply Uncompressed.Output.montgomery_words (source := stackPtr t+312)
  · rwa [source]
  · exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)
  · exact readable_of_grow
      (ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)) effect.agrees.grow
  · intro j hj
    have values := effect.writes
    simp only [yEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.2.1

theorem transfer_x [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x1102d4)
    (input : Field.MontgomeryAt t (stackPtr s - 480) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110308 ∧
      Field.MontgomeryAt u (stackPtr s - 664) value ∧
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
    (programText_slice (programLoaded_codeIn state.loaded) 0x102d4 xBytes
      (by decide) (by decide +kernel)) hp
  have writes : Uncompressed.Curve.StackWrites t (xEffect t).components := by
    constructor
    · intro address count member
      simp only [xEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨96,rfl,by decide⟩
      · exact ⟨104,rfl,by decide⟩
      · exact ⟨112,rfl,by decide⟩
      · exact ⟨120,rfl,by decide⟩
    all_goals simp [xEffect,Effect.components]
  have frame := Uncompressed.Curve.after_stack pre state ready effect.agrees writes
  have source : stackPtr t + 280 = stackPtr s - 480 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have destination : stackPtr t + 96 = stackPtr s - 664 :=
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

theorem transfer_negateY [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110318)
    (input : Field.MontgomeryAt t (stackPtr s - 448) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110358 ∧
      Field.MontgomeryAt u (stackPtr s - 416) value ∧
      (negateYEffect t).Holds t u := by
  have hp : NegateYPre t := by
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
  obtain ⟨n,u,run,ready,_,effect⟩ := negateY_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10318 negateYBytes
      (by decide) (by decide +kernel)) hp
  have writes : Uncompressed.Curve.StackWrites t (negateYEffect t).components := by
    constructor
    · intro address count member
      simp only [negateYEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨344,rfl,by decide⟩
      · exact ⟨352,rfl,by decide⟩
      · exact ⟨360,rfl,by decide⟩
      · exact ⟨368,rfl,by decide⟩
    all_goals simp [negateYEffect,Effect.components]
  have frame := Uncompressed.Curve.after_stack pre state ready effect.agrees writes
  have source : stackPtr t + 312 = stackPtr s - 448 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have destination : stackPtr t + 344 = stackPtr s - 416 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  refine ⟨n,u,run,frame,effect.rip,?_,effect⟩
  rw [← destination]
  apply Uncompressed.Output.montgomery_words (source := stackPtr t+312)
  · rwa [source]
  · exact ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)
  · exact readable_of_grow
      (ScalarFrame.stack_readable pre.toCalleePre state (by decide) (by decide)) effect.agrees.grow
  · intro j hj
    have values := effect.writes
    simp only [negateYEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.2.1

theorem transfer_negateX [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {value : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110370)
    (input : Field.MontgomeryAt t (stackPtr s - 480) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1103b0 ∧
      Field.MontgomeryAt u (stackPtr s - 592) value ∧
      (negateXEffect t).Holds t u := by
  have hp : NegateXPre t := by
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
  obtain ⟨n,u,run,ready,_,effect⟩ := negateX_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10370 negateXBytes
      (by decide) (by decide +kernel)) hp
  have writes : Uncompressed.Curve.StackWrites t (negateXEffect t).components := by
    constructor
    · intro address count member
      simp only [negateXEffect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
      rcases member with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨168,rfl,by decide⟩
      · exact ⟨176,rfl,by decide⟩
      · exact ⟨184,rfl,by decide⟩
      · exact ⟨192,rfl,by decide⟩
    all_goals simp [negateXEffect,Effect.components]
  have frame := Uncompressed.Curve.after_stack pre state ready effect.agrees writes
  have source : stackPtr t + 280 = stackPtr s - 480 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have destination : stackPtr t + 168 = stackPtr s - 592 :=
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
    simp only [negateXEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.1
    · simpa only [Nat.reduceMul,Operand.read,BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_assoc,BitVec.reduceAdd] using values.2.2.2.1


theorem y_preserves {t u : RamState} (effect : (yEffect t).Holds t u)
    {offset len : Nat} (bound : offset + len ≤ 2^64)
    (apart : offset + len ≤ 128 ∨ 160 ≤ offset) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Uncompressed.Output.bytes_of_offsets effect.agrees bound
  intro address count member
  simp only [yEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
    Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨128,rfl,by decide,by omega⟩
  · exact ⟨136,rfl,by decide,by omega⟩
  · exact ⟨144,rfl,by decide,by omega⟩
  · exact ⟨152,rfl,by decide,by omega⟩


theorem x_preserves {t u : RamState} (effect : (xEffect t).Holds t u)
    {offset len : Nat} (bound : offset + len ≤ 2^64)
    (apart : offset + len ≤ 96 ∨ 128 ≤ offset) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Uncompressed.Output.bytes_of_offsets effect.agrees bound
  intro address count member
  simp only [xEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
    Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨96,rfl,by decide,by omega⟩
  · exact ⟨104,rfl,by decide,by omega⟩
  · exact ⟨112,rfl,by decide,by omega⟩
  · exact ⟨120,rfl,by decide,by omega⟩


theorem negateY_preserves {t u : RamState} (effect : (negateYEffect t).Holds t u)
    {offset len : Nat} (bound : offset + len ≤ 2^64)
    (apart : offset + len ≤ 344 ∨ 376 ≤ offset) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Uncompressed.Output.bytes_of_offsets effect.agrees bound
  intro address count member
  simp only [negateYEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
    Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨344,rfl,by decide,by omega⟩
  · exact ⟨352,rfl,by decide,by omega⟩
  · exact ⟨360,rfl,by decide,by omega⟩
  · exact ⟨368,rfl,by decide,by omega⟩


theorem negateX_preserves {t u : RamState} (effect : (negateXEffect t).Holds t u)
    {offset len : Nat} (bound : offset + len ≤ 2^64)
    (apart : offset + len ≤ 168 ∨ 200 ≤ offset) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Uncompressed.Output.bytes_of_offsets effect.agrees bound
  intro address count member
  simp only [negateXEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
    Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Component.mem.injEq,reduceCtorEq,Nat.reduceDiv] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨168,rfl,by decide,by omega⟩
  · exact ⟨176,rfl,by decide,by omega⟩
  · exact ⟨184,rfl,by decide,by omega⟩
  · exact ⟨192,rfl,by decide,by omega⟩

end P256.Proofs.Sec1.Affine.Compact.Copy
