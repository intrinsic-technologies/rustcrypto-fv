import Hkdf.Proofs.Common.StreamPadding.Execution.Control
import Hkdf.Proofs.Common.StreamPadding.Execution.Semantics

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.SHA256

theorem copy_summary {s t : RamState} (v : Variant) (last : Bool)
    (effect : (Stages.copyEffect v last s).Holds s t)
    (bound : (stackPtr s).toNat + v.frame + 8 < 2^32) :
    stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue v.stableReg = s.regValue v.stableReg ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control ∧
      MemoryWriteFrame s t (writes v (stackPtr s)) := by
  obtain ⟨rsp,rbx,rbp,mxcsr,fcw⟩ := stable_of_agrees_selected v effect.agrees
    (by cases v <;> simp [Stages.copyEffect, Effect.components, Write.component,
      Operand.component, Variant.stableIndex, Variant.stableReg, regIndex] <;> decide)
  exact ⟨rsp,rbx,rbp,mxcsr,fcw,
    effect.agrees.memoryWriteFrame (copy_writes v last s bound)⟩

set_option maxHeartbeats 800000 in
theorem copy_hash {s t : RamState} {hash : Array UInt32} (v : Variant) (last : Bool)
    (effect : (Stages.copyEffect v last s).Holds s t)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 v.hash) hash) :
    HashStateAt t (stackPtr s + BitVec.ofNat 64 v.hash) hash := by
  apply Hkdf.Proofs.Common.hashState_of_bytes words
  intro i hi
  apply effect.agrees.byte
  intro c hc covered
  simp only [Stages.copyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨j,hj,he⟩ := covered
  all_goals
    refine (RangeApart.offsets (stackPtr s) (len := 8) (b := v.hash) (count := 32)
      ?_ ?_ ?_) j hj i hi he.symm
  all_goals cases v <;> decide

end Hkdf.Proofs.Common.StreamPadding.Execution
