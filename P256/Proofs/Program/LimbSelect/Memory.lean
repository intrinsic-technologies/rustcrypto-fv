import P256.Proofs.Program.LimbSelect.State
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

open P256.Proofs.Program (memoryRegion_contains_add stack_region_end)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool} {count : Nat}

theorem output_contains (hp : Pre s boundary) {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add hp.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem source_contains (hp : Pre s boundary) {i : Nat} (hi : i < 32) :
    (registerRegion s .rdx 32).Contains (s.regValue .rdx + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add hp.sourceBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem stack_contains (hp : Pre s boundary) {i : Nat} (hi : i < 24) :
    (Stack.region s 80).Contains (stackPtr s - 72 + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add hp.stack.1 (len := 24) _ _ hi
  · have he := P256.Proofs.Program.stack_sub_toNat hp.stack (offset := 72) (by decide)
    change (stackPtr s).toNat - 80 ≤ (stackPtr s - 72).toNat
    change (stackPtr s - 72).toNat = (stackPtr s).toNat - 72 at he
    rw [he]
    omega
  · rw [stack_region_end]
    have he := P256.Proofs.Program.stack_sub_toNat hp.stack (offset := 72) (by decide)
    change (stackPtr s - 72).toNat + 24 ≤ (stackPtr s).toNat + 8
    change (stackPtr s - 72).toNat = (stackPtr s).toNat - 72 at he
    rw [he]
    have := (P256.Proofs.Program.stack_bounds hp.stack).1
    omega

theorem components_within (hp : Pre s boundary) (hc : count ≤ 4) :
    WritesWithin (components s count) #v[registerRegion s .rdi 32, Stack.region s 80] := by
  intro c hm a hv
  simp only [components, registers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
    try exact hv.elim
  · obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨Stack.region s 80, by simp, stack_contains hp hi⟩
  · obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨registerRegion s .rdi 32, by simp, output_contains hp (by omega)⟩

theorem loaded_of_agrees (hp : Pre s boundary) (hc : count ≤ 4)
    (h : AgreesExcept (components s count) s t) : ProgramLoaded t := by
  intro a b hf
  apply Eq.trans (h.byte _) (hp.loaded a b hf)
  intro c hm hv
  obtain ⟨region, hr, hin⟩ := components_within hp hc c hm a hv
  exact hp.avoids region (by simpa using hr) a hin (.inl ⟨b, hf⟩)

theorem LoopState.loaded (hp : Pre s boundary) (h : LoopState s t select count)
    (hc : count ≤ 4) : ProgramLoaded t := loaded_of_agrees hp hc h.agrees

theorem LoopState.rsi (hp : Pre s boundary) (h : LoopState s t select count) :
    t.regValue .rsi = 4 :=
  (h.agrees.read (r := 6) (n := 64) (by simp [components, registers])).trans hp.leftCount

theorem LoopState.rdx (h : LoopState s t select count) : t.regValue .rdx = s.regValue .rdx :=
  h.agrees.read (r := 2) (n := 64) (by simp [components, registers])

theorem LoopState.rdi (h : LoopState s t select count) : t.regValue .rdi = s.regValue .rdi :=
  h.agrees.read (r := 7) (n := 64) (by simp [components, registers])

theorem source_byte (hp : Pre s boundary) (hc : count ≤ 4)
    (h : AgreesExcept (components s count) s t) {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rdx + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hm hv
  simp only [components, registers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
    try exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    exact hp.sourceStack _ (source_contains hp hi) (he ▸ stack_contains hp hj)
  · obtain ⟨j, hj, he⟩ := hv
    exact hp.sourceOutput _ (source_contains hp hi) (he ▸ output_contains hp (by omega))

theorem output_byte (hp : Pre s boundary) (_hc : count ≤ 4)
    (h : AgreesExcept (components s count) s t) {i : Nat} (hi : i < 32) (hafter : 8*count ≤ i) :
    t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hm hv
  simp only [components, registers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
    try exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    have hsep := hp.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
    exact hsep _ (output_contains hp hi) (he ▸ stack_contains hp hj)
  · obtain ⟨j, hj, he⟩ := hv
    have hb : (s.regValue .rdi).toNat + 32 < 2^32 := hp.outputBounded
    have hn := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
    omega

theorem source_readable (hp : Pre s boundary)
    (h : AgreesExcept (components s count) s t) {i len : Nat} (hi : i + len ≤ 32) :
    MemReadable t (s.regValue .rdx + BitVec.ofNat 64 i) len := by
  have hb : (s.regValue .rdx).toNat + 32 < 2^32 := hp.sourceBounded
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro j hj
    rw [add_ofNat_add_ofNat]
    exact h.grow _ (Option.isSome_iff_exists.mpr (hp.sourceAllocated _
      (source_contains hp (by omega))))

theorem output_readable (hp : Pre s boundary)
    (h : AgreesExcept (components s count) s t) {i len : Nat} (hi : i + len ≤ 32) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 i) len := by
  have hb : (s.regValue .rdi).toNat + 32 < 2^32 := hp.outputBounded
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro j hj
    rw [add_ofNat_add_ofNat]
    exact h.grow _ (Option.isSome_iff_exists.mpr (hp.outputAllocated _
      (output_contains hp (by omega))))

theorem output_tables (hp : Pre s boundary) {i len : Nat}
    (hi : i + len ≤ 32) (hpos : 0 < len) :
    (s.regValue .rdi + BitVec.ofNat 64 i).toNat + len ≤ 0x1000 ∨
      0x3000 ≤ (s.regValue .rdi + BitVec.ofNat 64 i).toNat := by
  have hr := output_readable hp (AgreesExcept.refl (components s 0) s) hi
  apply P256.Proofs.Program.tables_interval_of_not_reserved hpos hr.low
  intro j hj hin
  apply hp.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hin)
  rw [add_ofNat_add_ofNat]
  exact output_contains hp (by omega)

end P256.Proofs.Program.LimbSelect
