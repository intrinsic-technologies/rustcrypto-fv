import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs

theorem pushSequenceFrame_covers {s : RamState} {reserve offset : Nat}
    (sources : List (BitVec 4)) (stack : Stack.Valid s reserve)
    (capacity : offset + 8 * sources.length ≤ reserve) {c : Component} {a : BitVec 64}
    (member : c ∈ pushSequenceFrame s offset sources) (covered : c.Covers a) :
    (Stack.region s reserve).Contains a.toNat := by
  induction sources generalizing offset with
  | nil => simp [pushSequenceFrame] at member
  | cons source rest ih =>
    simp only [pushSequenceFrame, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with (rfl | rfl | rfl) | member
    · exact covered.elim
    · obtain ⟨i, hi, rfl⟩ := covered
      have bound : offset + 8 ≤ reserve := by
        simp only [List.length_cons] at capacity
        omega
      apply memoryRegion_contains_add stack.1 (len := 8) _ _ hi
      · rw [stack_sub_toNat stack bound]
        change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - (offset + 8)
        omega
      · rw [stack_region_end, stack_sub_toNat stack bound]
        have := stack_bounds stack
        omega
    · exact covered.elim
    · apply ih (offset := offset + 8) _ member
      simp only [List.length_cons] at capacity
      omega

theorem pushSequence_frame {s t : RamState} {reserve offset : Nat}
    {sources : List (BitVec 4)} {cs : List Component}
    (stack : Stack.Valid s reserve) (capacity : offset + 8 * sources.length ≤ reserve)
    (agrees : AgreesExcept (pushSequenceFrame s offset sources ++ cs) s t)
    (noMemory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) :
    MemoryWriteFrame s t #v[Stack.region s reserve] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · exact ⟨Stack.region s reserve, by simp,
      pushSequenceFrame_covers sources stack capacity hc ha⟩
  · exact (noMemory c hc a ha).elim

end P256.Proofs.Program
