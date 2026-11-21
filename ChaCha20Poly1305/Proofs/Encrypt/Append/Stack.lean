import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Code
import X86Proofs.Instructions.Push.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open MemoryRoutines.Machine

theorem stack_bounds {s : RamState} {n : Nat} (hs : Stack.Valid s n) :
    n ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2 ^ 32 := by
  rcases hs with ⟨hb, _, hn, _⟩
  change n ≤ (stackPtr s).toNat at hn
  change (stackPtr s).toNat - n + ((stackPtr s).toNat + 8 -
    ((stackPtr s).toNat - n)) < 2 ^ 32 at hb
  exact ⟨hn, by omega⟩

theorem stack_slot_contains {s : RamState} {n k i : Nat} (hs : Stack.Valid s n)
    (hk : k ≤ n) (hi : i < k + 8) :
    (Stack.region s n).Contains
      (stackPtr s - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat := by
  obtain ⟨hn, ht⟩ := stack_bounds hs
  have he : (stackPtr s - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - k + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [he]
  change (stackPtr s).toNat - n ≤ _ ∧
    _ < (stackPtr s).toNat - n + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - n))
  omega

theorem stack_slot_readable {s u : RamState} {n k : Nat} (hs : Stack.Valid s n)
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (u.external[a]?).isSome) (hk : k ≤ n) :
    MemReadable u (stackPtr s - BitVec.ofNat 64 k) 8 := by
  obtain ⟨hn, ht⟩ := stack_bounds hs
  refine ⟨?_, fun i hi => hg _ ?_⟩
  · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · obtain ⟨b, hb⟩ := hs.2.1 _ (stack_slot_contains (i := i) hs hk (by omega))
    simp only [hb, Option.isSome_some]

theorem stack_slot_writable {s u : RamState} {n k : Nat} (hs : Stack.Valid s n)
    (ha : (Stack.region s n).Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (u.external[a]?).isSome) (hk : k ≤ n) :
    MemWritable u (stackPtr s - BitVec.ofNat 64 k) 8 := by
  obtain ⟨hn, ht⟩ := stack_bounds hs
  have hr := stack_slot_readable hs hg hk
  refine ⟨hr.low, hr.mem, ?_⟩
  have he : (stackPtr s - BitVec.ofNat 64 k).toNat = (stackPtr s).toNat - k := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [he]
  unfold PageTableEntriesApart
  apply Classical.byContradiction
  intro h
  let x := max ((stackPtr s).toNat - k) 0x1000
  have hx : x < 2 ^ 64 := by dsimp [x]; omega
  apply ha (BitVec.ofNat 64 x)
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    change (stackPtr s).toNat - n ≤ x ∧
      x < (stackPtr s).toNat - n + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - n))
    dsimp [x]; omega
  · right
    simp only [pageTables, MemoryRegion.Contains, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    dsimp [x]; omega

theorem stack_slot_avoids {s : RamState} {n k : Nat} (hs : Stack.Valid s n)
    (ha : (Stack.region s n).Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hk : k ≤ n) :
    ∀ a, (Component.mem (stackPtr s - BitVec.ofNat 64 k) 8).Covers a → ¬ InProgram a := by
  rintro _ ⟨i, hi, rfl⟩ hp
  exact ha _ (stack_slot_contains (i := i) hs hk (by omega)) (Or.inl hp)

theorem stack_store_pre {s u : RamState} {n k len : Nat} {p : BitVec 64}
    {addr : RamState → BitVec 64} (hs : Stack.Valid s n)
    (ha : (Stack.region s n).Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (u.external[a]?).isSome) (hk : k ≤ n) (hr :
        u.RIP = p)
    (he : addr u = stackPtr s - BitVec.ofNat 64 k)
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) :
    StorePre p len addr 8 u := by
  refine ⟨hr, he ▸ stack_slot_writable hs ha hg hk, ?_⟩
  rw [he]
  intro i hi j hj eq
  exact stack_slot_avoids hs ha hk _ ⟨i, hi, rfl⟩ (eq.symm ▸ hp j hj)

theorem stack_push_run [Bindings] {s u : RamState} {n k len : Nat}
    {p : BitVec 64} {src : BitVec 5} {bytes : List UInt8} {boundary : ReturnBoundary}
    (hs : Stack.Valid s n)
    (ha : (Stack.region s n).Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (u.external[a]?).isSome) (hk : k ≤ n)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hbytes : CodeIn (codeRange p bytes) u)
    (hstep : StepEffect (PushPre p len) (codeRange p bytes) (pushR64Effect p len src))
    (hrip : u.RIP = p) (haddr : pushAddr u = stackPtr s - BitVec.ofNat 64 k)
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j))
    (hne : p + BitVec.ofNat 64 len ≠ boundary.rip) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (pushR64Effect p len src u).Holds u v := by
  obtain ⟨v, adv, ready, eff⟩ := hstep.advances hr hbytes
    (stack_store_pre hs ha hg hk hrip haddr hp) hne
  refine ⟨v, adv, ready, eff.codeIn ?_ hc, eff⟩
  intro x hx c hmem hcover
  have hprogram := inProgram_of_mem hx
  simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hcover.elim
  · rw [haddr] at hcover
    exact stack_slot_avoids hs ha hk x.1 hcover hprogram
  · exact hcover.elim

end ChaCha20Poly1305.Proofs.Encrypt
