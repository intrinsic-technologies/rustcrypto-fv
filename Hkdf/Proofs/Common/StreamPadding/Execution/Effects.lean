import Hkdf.Proofs.Common.StreamPadding.Stages
import Hkdf.Proofs.Common.StreamPadding.Execution.Geometry

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Stages

theorem stable_of_agrees_selected (v : Variant) {s t : RamState} {components : List Component}
    (agrees : AgreesExcept components s t)
    (kept : ∀ c ∈ ([.reg 4, .reg 3, .reg v.stableIndex, .mxcsr, .fcw] : List Component),
      c ∉ components) :
    stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue v.stableReg = s.regValue v.stableReg ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control := by
  exact ⟨agrees.read (n := 64) (r := 4) (kept _ (by simp)),
    agrees.read (n := 64) (r := 3) (kept _ (by simp)),
    reg_agrees agrees v.stableReg (kept _ (by simp [Variant.stableIndex])),
    agrees.mxcsr (kept _ (by simp)), agrees.fcw (kept _ (by simp))⟩

theorem stable_of_agrees {s t : RamState} {components : List Component}
    (agrees : AgreesExcept components s t)
    (kept : ∀ c ∈ ([.reg 4, .reg 3, .reg 5, .mxcsr, .fcw] : List Component),
      c ∉ components) :
    stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue .rbp = s.regValue .rbp ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control :=
  stable_of_agrees_selected .key agrees kept

theorem load_noMem (v : Variant) (s : RamState) :
    ∀ c ∈ (loadEffect v s).components, ∀ a, ¬ c.Covers a := by
  simp [loadEffect, Effect.components, Write.component, Operand.component, Component.Covers]


theorem mark_writes (v : Variant) (s : RamState) (remaining : Nat)
    (bound : (stackPtr s).toNat + v.frame + 8 < 2^32)
    (length : s.regValue v.lengthReg = BitVec.ofNat 64 remaining) (small : remaining < 64) :
    WritesWithin (markEffect v s).components (writes v (stackPtr s)) := by
  intro c member a covered
  simp only [markEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl | rfl) | rfl) | rfl
  all_goals try exact covered.elim
  change (Component.mem (stackPtr s + (.reg v.lengthIndex : Operand 64).read s + BitVec.ofNat 64 v.tail) 1).Covers a at covered
  simp only [Variant.lengthIndex, read_regIndex, BitVec.setWidth_eq] at covered
  rw [length, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 remaining),
    ← BitVec.ofNat_add] at covered
  refine ⟨⟨(stackPtr s + BitVec.ofNat 64 v.tail).toNat,64⟩, by simp [writes], ?_⟩
  apply offset_component (stackPtr s) (v.tail+remaining) 1 v.tail 64 ?_ (by omega) (by omega) a covered
  have shape : v.tail + 64 ≤ v.frame + 8 := by cases v <;> decide
  omega

theorem copy_writes (v : Variant) (last : Bool) (s : RamState)
    (bound : (stackPtr s).toNat + v.frame + 8 < 2^32) :
    WritesWithin (copyEffect v last s).components (writes v (stackPtr s)) := by
  intro c member a covered
  simp only [copyEffect, Effect.components, List.map_append, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl
  all_goals try exact covered.elim
  all_goals refine ⟨⟨(stackPtr s + BitVec.ofNat 64 v.scratch).toNat,64⟩, by simp [writes], ?_⟩
  all_goals apply offset_component (stackPtr s) _ 8 v.scratch 64 ?_ (by omega) (by omega) a covered
  all_goals have shape : v.scratch + 64 ≤ v.frame + 8 := by cases v <;> decide
  all_goals omega

theorem zero_writes (v : Variant) (s : RamState)
    (bound : (stackPtr s).toNat + v.frame + 8 < 2^32) :
    WritesWithin (zeroEffect v s).components (writes v (stackPtr s)) := by
  intro c member a covered
  simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact covered.elim
  all_goals refine ⟨⟨(stackPtr s + BitVec.ofNat 64 v.tail).toNat,64⟩, by simp [writes], ?_⟩
  all_goals apply offset_component (stackPtr s) _ 8 v.tail 64 ?_ (by omega) (by omega) a covered
  all_goals have shape : v.tail + 64 ≤ v.frame + 8 := by cases v <;> decide
  all_goals omega

theorem length_writes (v : Variant) (s : RamState)
    (bound : (stackPtr s).toNat + v.frame + 8 < 2^32) :
    WritesWithin (lengthEffect v s).components (writes v (stackPtr s)) := by
  intro c member a covered
  simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl) | rfl) | rfl
  all_goals try exact covered.elim
  refine ⟨⟨(stackPtr s + BitVec.ofNat 64 v.tail).toNat,64⟩, by simp [writes], ?_⟩
  apply offset_component (stackPtr s) _ 8 v.tail 64 ?_ (by omega) (by omega) a covered
  have shape : v.tail + 64 ≤ v.frame + 8 := by cases v <;> decide
  omega

end Hkdf.Proofs.Common.StreamPadding.Execution
