import P256.Proofs.Verifying.Combination.Naf.Machine.LoopState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Start

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

def components (s : RamState) (cells : List (Nat × Nat)) : List Component :=
  [.reg 0, .reg 5, .reg 13, .reg 14, .reg 15, .flags, .rip] ++
    cells.map (fun cell => .mem (stackPtr s - BitVec.ofNat 64 cell.1) cell.2)

theorem writes [Bindings] {s : RamState} {boundary : ReturnBoundary} {cells : List (Nat × Nat)}
    (pre : Pre s boundary) (bounds : ∀ cell ∈ cells, cell.1 ≤ 168 ∧ cell.2+48 ≤ cell.1) :
    WritesWithin (components s cells) #v[registerRegion s .rdi 257, workRegion s] := by
  intro c hc a ha
  simp only [components, List.mem_append, List.mem_map] at hc
  rcases hc with hc | ⟨cell, hcell, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ha.elim
  · exact ⟨workRegion s, by simp, work_contains pre.toCalleePre
      (bounds cell hcell).1 (bounds cell hcell).2 ha⟩

theorem byte [Bindings] {s t w : RamState} {boundary : ReturnBoundary} {cells : List (Nat × Nat)}
    (pre : Pre s boundary) (agrees : AgreesExcept (components s cells) t w)
    (bounds : ∀ cell ∈ cells, cell.1 ≤ 168 ∧ cell.2 ≤ cell.1+8)
    {off len : Nat} (ho : off ≤ 168) (hl : len ≤ off+8)
    (apart : ∀ cell ∈ cells, off+cell.2 ≤ cell.1 ∨ cell.1+len ≤ off)
    {i : Nat} (hi : i<len) :
    w.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? := by
  have stackBounds := stack_bounds pre.stack
  have offNat := stack_sub_toNat pre.stack ho
  apply agrees.byte
  intro c hc ha
  simp only [components, List.mem_append, List.mem_map] at hc
  rcases hc with hc | ⟨cell, hcell, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ha.elim
  · have limits := bounds cell hcell
    have cellNat := stack_sub_toNat pre.stack limits.1
    have separation := apart cell hcell
    obtain ⟨j, hj, he⟩ := ha
    have hh := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by rw [offNat]; omega),
      toNat_add_ofNat _ _ (by rw [cellNat]; omega), offNat, cellNat] at hh
    omega

theorem read [Bindings] {s t w : RamState} {boundary : ReturnBoundary} {cells : List (Nat × Nat)}
    (pre : Pre s boundary) (agrees : AgreesExcept (components s cells) t w)
    (bounds : ∀ cell ∈ cells, cell.1 ≤ 168 ∧ cell.2 ≤ cell.1+8)
    {off n : Nat} (ho : off ≤ 168) (hl : n/8 ≤ off+8)
    (apart : ∀ cell ∈ cells, off+cell.2 ≤ cell.1 ∨ cell.1+n/8 ≤ off) :
    memLoad w.external (stackPtr s-BitVec.ofNat 64 off) n =
      memLoad t.external (stackPtr s-BitVec.ofNat 64 off) n := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun v : Option UInt8 => v.getD 0) (byte pre agrees bounds ho hl apart hi)

end P256.Proofs.Verifying.Combination.Naf.Machine.Start

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem StateAt.of_copy {s t : RamState} {address destination source : BitVec 64} {n k : Nat}
    (state : StateAt s address source n k)
    (bytes : ∀ i<40, t.external[destination+BitVec.ofNat 64 i]? = s.external[address+BitVec.ofNat 64 i]?) :
    StateAt t destination source n k := by
  have word (off : Nat) (ho : off+8 ≤ 40) :
      memLoad t.external (destination+BitVec.ofNat 64 off) 64 =
        memLoad s.external (address+BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[destination+BitVec.ofNat 64 off+BitVec.ofNat 64 i]?).getD 0 =
      (s.external[address+BitVec.ofNat 64 off+BitVec.ofNat 64 i]?).getD 0
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun v : Option UInt8 => v.getD 0) (bytes (off+i) (by omega))
  refine ⟨?_, (word 8 (by decide)).trans state.remaining,
    (word 16 (by decide)).trans state.index, (word 24 (by decide)).trans state.low,
    (word 32 (by decide)).trans state.high⟩
  have h := word 0 (by decide)
  simp only [BitVec.add_zero] at h
  exact h.trans state.pointer

end P256.Proofs.Verifying.Combination.Naf.Iterator
