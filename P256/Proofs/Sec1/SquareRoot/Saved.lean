import P256.Proofs.Sec1.SquareRoot.Entry
import P256.Proofs.Program.ScalarFrame.Work
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r12, 32), (.rbx, 40)]

structure SavedWords (s t : RamState) : Prop where
  saved : ∀ slot ∈ savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 slot.2) 64 = s.regValue slot.1
  returnAddress : memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip

theorem entry_saved_words {s t : RamState} (memory : t.external = entryMemory s) :
    SavedWords s t := by
  constructor
  · intro slot hslot
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hslot
    rcases hslot with rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [memory]
      simp only [entryMemory, savedSources, pushSequenceMemory, Nat.reduceAdd,
        BitVec.sub_eq_add_neg]
      repeat rw [memLoad_memStore_apart _ _ _ _ _ 64
        (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    rw [memory]
    simp only [entryMemory, savedSources, pushSequenceMemory, Nat.reduceAdd,
      BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem SavedWords.after_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (saved : SavedWords s t)
    (frame : MemoryWriteFrame t u
      #v[registerRegion s .rdi 40, ScalarFrame.Work.region s 2176 40]) : SavedWords s u := by
  have read (offset : Nat) (bound : offset ≤ 40) :
      memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    ScalarFrame.Work.read pre (by decide) frame bound (by omega)
  constructor
  · intro slot hslot
    apply (read slot.2 ?_).trans (saved.saved slot hslot)
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hslot
    rcases hslot with rfl | rfl | rfl | rfl | rfl <;> decide
  · have h := read 0 (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans saved.returnAddress

end P256.Proofs.Sec1.SquareRoot
