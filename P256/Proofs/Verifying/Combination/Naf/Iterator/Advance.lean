import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Core
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

set_option maxHeartbeats 1600000 in
theorem advance_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {source : BitVec 64} {n k q : Nat}
    (pre : AdvancePre s boundary source) (input : Nat256At s source n)
    (state : StateAt s (s.regValue .rdi) source n k)
    (requested : s.regValue .rsi = BitVec.ofNat 64 q)
    (step : q=k ∨ q=k+1) (bound : q<4) :
    ∃ t, CalleeResult s t boundary 40 24 ∧ StateAt t (s.regValue .rdi) source n q ∧
      t.regValue .rax = word n q ∧ t.regValue .rdx = word n (q+1) ∧ Nat256At t source n := by
  obtain ⟨u, run0, ready0, loaded0, rip0, sp0, mem0, ag0⟩ :=
    Advance.prologue pre.toCalleePre (by decide)
  have up : u.regValue .rdi = s.regValue .rdi := ag0.read (n := 64) (r := 7) (by simp [Initialize.saveFrame])
  have frame0 : MemoryWriteFrame s u #v[Stack.region s 24] := by
    apply ag0.memoryWriteFrame
    intro c hc a cover
    simp only [Initialize.saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    · exact ⟨_, by simp, stackRegion_contains_sub (offset := 8) pre.stack.2.2.1 (by decide) (by decide) cover⟩
    · exact ⟨_, by simp, stackRegion_contains_sub (offset := 16) pre.stack.2.2.1 (by decide) (by decide) cover⟩
    · exact ⟨_, by simp, stackRegion_contains_sub (offset := 24) pre.stack.2.2.1 (by decide) (by decide) cover⟩
  have outputRead (offset : Nat) (ho : offset+8 ≤ 40) :
      memLoad u.external (s.regValue .rdi + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (s.regValue .rdi + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (u.external[s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
    rw [frame0 _]
    intro region hr hin
    have eq : region = Stack.region s 24 := by simpa using hr
    subst region
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hin
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change offset+i<40; omega)
  have state0 : StateAt u (u.regValue .rdi) source n k := by
    rw [up]
    constructor
    · have h := outputRead 0 (by decide)
      simp only [BitVec.add_zero] at h
      exact h.trans state.pointer
    · exact (outputRead 8 (by decide)).trans state.remaining
    · exact (outputRead 16 (by decide)).trans state.index
    · exact (outputRead 24 (by decide)).trans state.low
    · exact (outputRead 32 (by decide)).trans state.high
  have input0 : Nat256At u source n := by
    refine ⟨input.1, fun i hi => ?_⟩
    rw [frame0 _]
    · exact input.2 i hi
    · intro region hr hin
      have eq : region = Stack.region s 24 := by simpa using hr
      subst region
      exact pre.sourceStack _ (memoryRegion_contains_add pre.sourceBounded (Nat.le_refl _) (Nat.le_refl _) hi) hin
  have write0 : Writable u (u.regValue .rdi) 40 := by
    rw [up]
    have hr : MemReadable u (s.regValue .rdi) 40 :=
      readable_of_grow
        (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)) ag0.grow
    refine ⟨hr, tables_of_not_reserved (by decide) hr.low ?_⟩
    intro i hi hin
    exact pre.avoids (registerRegion s .rdi 40) (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hin)
  have bounded0 : (registerRegion u .rdi 40).Bounded := by
    change (⟨(u.regValue .rdi).toNat,40⟩ : MemoryRegion).Bounded
    rw [up]; exact pre.outputBounded
  have avoid0 : ∀ i < 40, ¬ InProgram (u.regValue .rdi + BitVec.ofNat 64 i) := by
    intro i hi hp
    rw [up] at hp
    exact pre.avoids (registerRegion s .rdi 40) (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inl hp)
  have source0 : MemReadable u source 32 :=
    readable_of_grow
      (memoryRegion_memReadable pre.sourceBounded pre.sourceAllocated (Nat.le_refl _) (Nat.le_refl _)) ag0.grow
  have apart0 : (⟨source.toNat,32⟩ : MemoryRegion).Disjoint (registerRegion u .rdi 40) := by
    change (⟨source.toNat,32⟩ : MemoryRegion).Disjoint ⟨(u.regValue .rdi).toNat,40⟩
    rw [up]; exact pre.sourceOutput
  have request0 : u.regValue .rsi = BitVec.ofNat 64 q :=
    (ag0.read (n := 64) (r := 6) (by simp [Initialize.saveFrame])).trans requested
  obtain ⟨fuel, v, runV, readyV, loadedV, ripV, stateV, vx, vd, agV⟩ :=
    Advance.core ready0 loaded0 rip0 state0 write0 bounded0 avoid0 pre.sourceBounded source0 apart0
      input0 request0 step bound pre.outerBoundary
  rw [up] at stateV agV
  have outputFrame : MemoryWriteFrame u v #v[registerRegion s .rdi 40] :=
    Advance.core_frame pre.outputBounded agV
  have frame : MemoryWriteFrame s v #v[registerRegion s .rdi 40, Stack.region s 24] := by
    intro a ha
    rw [outputFrame a (by
      intro region hr hin
      have eq : region = registerRegion s .rdi 40 := by simpa using hr
      exact ha _ (by simp [eq]) hin)]
    exact frame0 a (by
      intro region hr hin
      have eq : region = Stack.region s 24 := by simpa using hr
      exact ha _ (by simp [eq]) hin)
  have stackRead (offset : Nat) (ho : offset ≤ 24) :
      memLoad v.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (v.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
      (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
    rw [outputFrame _]
    intro region hr hin
    have eq : region = registerRegion s .rdi 40 := by simpa using hr
    subst region
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    have bounds := stack_bounds pre.stack
    have low := stack_sub_toNat pre.stack ho
    change (stackPtr s).toNat - 24 ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region s 24).start + (Stack.region s 24).size
    rw [stack_region_end, toNat_add_ofNat _ _ (by rw [low]; omega), low]
    constructor <;> omega
  have epi : Advance.EpiloguePre s v := by
    refine ⟨readyV, loadedV, ripV, ?_, ag0.trans agV, frame, ?_, ?_, ?_⟩
    · exact (agV.read (n := 64) (r := 4) (by simp [Advance.coreComponents])).trans sp0
    · change memLoad v.external (stackPtr s - 16#64) 64 = s.regValue .rbx
      rw [stackRead 16 (by decide), mem0]; exact Initialize.saveMemory_rbx s
    · change memLoad v.external (stackPtr s - 8#64) 64 = s.regValue .r14
      rw [stackRead 8 (by decide), mem0]; exact Initialize.saveMemory_r14 s
    · have h := stackRead 0 (by decide)
      simp only [BitVec.sub_zero] at h
      rw [h, mem0]; exact Initialize.saveMemory_return s
  obtain ⟨t, result, memory, tx, td⟩ := Advance.epilogue pre.toCalleePre epi ⟨3+fuel, run0.trans runV⟩
  refine ⟨t, result, Advance.state_of_external stateV memory, tx.trans vx, td.trans vd, input.1, ?_⟩
  intro i hi
  rw [result.frame _]
  · exact input.2 i hi
  · intro region hr hin
    have eq : region = registerRegion s .rdi 40 ∨ region = Stack.region s 24 := by simpa using hr
    have hsource := memoryRegion_contains_add pre.sourceBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rcases eq with rfl | rfl
    · exact pre.sourceOutput _ hsource hin
    · exact pre.sourceStack _ hsource hin

end P256.Proofs.Verifying.Combination.Naf.Iterator
