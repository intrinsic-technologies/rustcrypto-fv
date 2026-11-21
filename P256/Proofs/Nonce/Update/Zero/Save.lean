import P256.Proofs.Nonce.Update.Zero.SaveRun
import P256.Proofs.Nonce.Update.Zero.State
import P256.Proofs.Nonce.Update.Zero.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.HMAC.Key.Output.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero.Save

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {original state : State} {input : ByteArray}

theorem store_pre (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Hashed initial s state input) : StorePre s := by
  have pointer : keyPointer s = initial.regValue .rdi := by
    change memLoad s.external (stackPtr s + 72) 64 = _
    rw [current.rsp]
    exact current.savedPointer
  refine ⟨current.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_readable pre.callee current.toFrameState (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_writable pre.callee current.toFrameState (by decide) (by decide) (by decide)
  · intro i hi pc len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ScalarFrame.stack_code pre.callee current.toFrameState (by decide) (by decide) bound
  · have writable := ScalarFrame.output_writable pre.callee (by decide) current.allocated
    intro i hi
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact writable.add _ (by decide)
  · intro i hi pc len bound
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, k ≤ 24 ∧ i = BitVec.ofNat 64 k := by
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨24, by decide, rfl⟩
    exact fun a ha b hb eq => (ScalarFrame.output_code pre.callee bound)
      (k + a) (by omega) b hb (by simpa only [BitVec.ofNat_add, BitVec.add_assoc] using eq)
  · intro i hi j hj a ha b hb eq
    rw [pointer] at eq
    obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, k ≤ 24 ∧ i = BitVec.ofNat 64 k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨24, by decide, rfl⟩
    obtain ⟨l, hl, rfl⟩ : ∃ l : Nat, l ≤ 24 ∧ j = BitVec.ofNat 64 l := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨24, by decide, rfl⟩
    have inside := ScalarFrame.output_contains pre.callee (offset := k) (len := 8) (by omega) ⟨a, ha, rfl⟩
    have stk : (Stack.region initial 1856).Contains
        (rspOf s + BitVec.ofNat 64 l + BitVec.ofNat 64 b).toNat := by
      change (Stack.region initial 1856).Contains
        (stackPtr s + BitVec.ofNat 64 l + BitVec.ofNat 64 b).toNat
      rw [current.rsp]
      exact work_substack pre (work_contains_scratch pre (by omega) ⟨b, hb, rfl⟩)
    rw [eq] at inside
    exact pre.separation _ inside stk

def components (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 7, .reg 3, .reg 6,
    .mem (scratch initial + 0) 32, .mem (initial.regValue .rdi) 32, .rip]

theorem store (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Hashed initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧
      ValueReady initial t ⟨Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key input, state.value⟩ := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := store_run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported)
    (programText_slice (programLoaded_codeIn current.loaded) 0xa3f7 storeBytes
      (by decide) (by decide +kernel)) (store_pre pre current)
  have pointer : keyPointer s = initial.regValue .rdi := by
    change memLoad s.external (stackPtr s + 72) 64 = _
    rw [current.rsp]
    exact current.savedPointer
  have agrees : AgreesExcept (components initial) s t := by
    apply effect.agrees.widen
    · simp [storeEffect, Effect.components, Component.isMem, components]
    · intro a c hc ha
      have hc : c = .reg 0 ∨ c = .reg 1 ∨ c = .reg 2 ∨ c = .reg 7 ∨ c = .reg 3 ∨ c = .reg 6 ∨
          c = .mem (stackPtr s + 24) 8 ∨ c = .mem (stackPtr s + 16) 8 ∨
          c = .mem (stackPtr s + 8) 8 ∨ c = .mem (stackPtr s + 0) 8 ∨
          c = .mem (keyPointer s + 24) 8 ∨ c = .mem (keyPointer s + 16) 8 ∨
          c = .mem (keyPointer s + 8) 8 ∨ c = .mem (keyPointer s + 0) 8 ∨ c = .rip := by
        simpa [storeEffect, Effect.components, stackPtr] using hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals obtain ⟨i, hi, rfl⟩ := ha
      all_goals first
        | (refine ⟨.mem (scratch initial + 0) 32, by simp [components], ?_⟩
           rw [current.rsp])
        | refine ⟨.mem (initial.regValue .rdi) 32, by simp [components], ?_⟩
      · exact ⟨24+i, by omega, by try simp only [scratch]; bv_omega⟩
      · exact ⟨16+i, by omega, by try simp only [scratch]; bv_omega⟩
      · exact ⟨8+i, by omega, by try simp only [scratch]; bv_omega⟩
      · exact ⟨i, by omega, rfl⟩
      all_goals rw [pointer]
      · exact ⟨24+i, by omega, by bv_omega⟩
      · exact ⟨16+i, by omega, by bv_omega⟩
      · exact ⟨8+i, by omega, by bv_omega⟩
      · exact ⟨i, by omega, by bv_omega⟩
  have frame : FrameState initial t := by
    apply ScalarFrame.FrameState.after_effect pre.callee (by decide) current.toFrameState ready agrees
    · intro c hc a ha
      simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      · exact ⟨ScalarFrame.workRegion initial 1856, by simp,
          work_contains_scratch pre (offset := 0) (by decide) ha⟩
      · exact ⟨registerRegion initial .rdi 64, by simp,
          ScalarFrame.output_contains pre.callee (offset := 0) (len := 32) (by decide)
            (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha)⟩
    · simp [components]
  have value : (MemoryRegion.mk (initial.regValue .rdi + 32).toNat 32).HasBytes
      t.external state.value := by
    apply hasBytes_copy current.drbg.2
    intro i hi
    apply agrees.byte
    intro c hc ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact pre.separation _ (ScalarFrame.output_contains pre.callee (offset := 32) (len := 32)
        (by decide) ⟨i, hi, rfl⟩)
        (work_substack pre (work_contains_scratch pre (offset := 0) (by decide) ha))
    · obtain ⟨j, hj, eq⟩ := ha
      exact RangeApart.offsets (initial.regValue .rdi) (a := 0) (b := 32)
        (by decide) (by decide) (.inl (by decide)) j hj i hi
        (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq.symm)
  have words : ∀ j < 4,
      memLoad t.external (initial.regValue .rdi + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (scratch initial + 256 + BitVec.ofNat 64 (8*j)) 64 := by
    have h := effect.writes
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
      memLoad t.external (keyPointer s + 24) 64 = memLoad s.external (stackPtr s + 280) 64 ∧
      memLoad t.external (keyPointer s + 16) 64 = memLoad s.external (stackPtr s + 272) 64 ∧
      memLoad t.external (keyPointer s + 8) 64 = memLoad s.external (stackPtr s + 264) 64 ∧
      memLoad t.external (keyPointer s + 0) 64 = memLoad s.external (stackPtr s + 256) 64 at h
    rw [pointer, current.rsp] at h
    have h := h.2.2.2.2.2.2.2.2.2.2
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [scratch, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.2.2.2
    · simpa only [scratch, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.2.2.1
    · simpa only [scratch, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.2.1
    · simpa only [scratch, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.1
  have digest : (MemoryRegion.mk (initial.regValue .rdi).toNat 32).HasBytes t.external
      (Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key input) := by
    apply hasBytes_copy current.output
    apply HMAC.Key.Output.bytes_of_words (count := 4)
    · have h := ScalarFrame.stack_readable pre.callee current.toFrameState
        (offset := 256) (len := 32) (by decide) (by decide)
      simpa only [scratch, current.rsp, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
    · exact readable_of_grow
        (memoryRegion_memReadable pre.stateBounded pre.stateAllocated
          (Nat.le_refl _) (by change (initial.regValue .rdi).toNat + 4 * 8 ≤
            (initial.regValue .rdi).toNat + 64; omega)) frame.allocated
    · exact words
  have keep : ∀ offset ∈ ([64,72,80,424] : List Nat), ∀ i < 8,
      t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro offset member i hi
    have cases : offset = 64 ∨ offset = 72 ∨ offset = 80 ∨ offset = 424 := by simpa using member
    apply agrees.byte
    intro c hc ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · obtain ⟨j, hj, equal⟩ := ha
      exact RangeApart.offsets (scratch initial) (a := 0) (b := offset)
        (len := 32) (count := 8) (by decide) (by omega) (.inl (by omega)) j hj i hi equal.symm
    · exact pre.separation _
        (ScalarFrame.output_contains pre.callee (offset := 0) (len := 32) (by decide)
          (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha))
        (work_substack pre (work_contains_scratch pre (by omega) ⟨i, hi, rfl⟩))
  have context := current.toContext.of_copied frame (show DrbgAt t (initial.regValue .rdi)
      ⟨Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key input, state.value⟩ from ⟨digest, value⟩)
    ((agrees.read (n := 64) (r := 5) (by simp [components])).trans current.descriptors) keep
  exact ⟨fuel, t, run, context, effect.rip,
    effect.writes.2.2.2.1.trans pointer, effect.writes.2.2.2.2.1.trans pointer⟩

end P256.Proofs.Nonce.Update.Zero.Save
