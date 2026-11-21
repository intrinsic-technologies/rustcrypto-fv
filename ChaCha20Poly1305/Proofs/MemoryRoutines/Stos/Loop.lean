import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos.Invariant
import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos.Step
import X86Proofs.Program.Execution

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs

theorem ReadyLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {kind : Kind} {s : RamState} {count : Nat} (h : ReadyLoop kind s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (repStosAfter kind s)) := by
  have hdl := h.dstLow
  have hal := h.dstAlign
  have hle : kind.bytes ≤ kind.bytes * count := Nat.le_mul_of_pos_right _ hpos
  exact rep_stos_step hstride kind s h.ready h.df h.code h.codeLow (h.rcx_ne hpos)
    (by omega) (by cases kind <;> simp only [Kind.bytes] at hal ⊢ <;> omega)
    (fun i hi ↦ h.dstMem i (by omega))

theorem rep_stos_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (count : Nat) (s : RamState) (h : ReadyLoop kind s (count + 1)) :
    Done kind s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext := nextState_of_step (h.step hstride (by omega))
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by rw [h.counter]; rfl
    have hflag : (repStosAfter kind s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (repStosAfter_ready kind h.ready (by simpa using h.dstTables)).ready hflag
    · rw [repStosAfter_rip kind s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · simpa only [Nat.zero_add, Nat.mul_one] using repStosAfter_rdi kind s
    · intro i hi
      have hi' : i < kind.bytes := by simpa using hi
      rw [Nat.mod_eq_of_lt hi']
      exact repStosAfter_fill kind s i hi'
    · rw [← clearRep_eq hflag]
      simpa only [Nat.zero_add, Nat.mul_one] using repStosAfter_agrees kind s
  | succ k ih =>
    have hnext := nextState_of_step (h.step hstride (by omega))
    have hdl := h.dstLow
    have hsize : kind.bytes * (k + 1 + 1) = kind.bytes + kind.bytes * (k + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]; omega
    have hfirst (i : Nat) (hi : i < kind.bytes) := repStosAfter_fill kind s i hi
    have ih' := ih (repStosAfter kind s) h.next
    rw [nextStates_succ, hnext]
    refine ⟨ih'.ready, by rw [ih'.rip, h.next_rip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, repStosAfter_rdi, add_ofNat_add_ofNat, hsize]
    · intro i hi
      by_cases hsmall : i < kind.bytes
      · rw [Nat.mod_eq_of_lt hsmall]
        refine (ih'.agrees.byte ?_).trans (hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [repStosAfter_rdi, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.fill (i - kind.bytes) (by omega)
        rw [repStosAfter_rdi, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          repStosAfter_rax] at hc
        have hm : (i - kind.bytes) % kind.bytes = i % kind.bytes := by
          have he : i = kind.bytes + (i - kind.bytes) := by omega
          conv => rhs; rw [he, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
        rw [hm] at hc
        exact hc
    · refine (repStosAfter_agrees kind s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (kind.bytes * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [repStosAfter_rdi, add_ofNat_add_ofNat] at he
          exact ⟨kind.bytes + j, by omega, he⟩

theorem ReadyLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (boundary : ReturnBoundary) (count : Nat) (s : RamState)
    (h : ReadyLoop kind s (count + 1)) (hstart : s.RIP ≠ boundary.rip)
    (hend : BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length) ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride (by omega)
    have hi : (repStosAfter kind s).RIP ≠ boundary.rip := by
      rw [repStosAfter_rip kind s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride (by omega)
    have ha : Advances boundary 1 s (repStosAfter kind s) :=
      Advances.of_step hs (.inl (by rw [h.next_rip]; exact hstart))
    have hb := ih (repStosAfter kind s) h.next (by rw [h.next_rip]; exact hstart)
      (by rw [h.next_rip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

end ChaCha20Poly1305.Proofs.MemoryRoutines.Stos
