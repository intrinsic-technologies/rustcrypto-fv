import P256.Proofs.Sec1Serialize.Tail.Initialize.State
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Zeroing [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) (infinity : Bool) (offset : Nat) : Prop where
  state : FrameState s t 65 328 312
  execution : ∃ n, Advances boundary n s t
  destination : t.regValue .rbp = s.regValue .rdi
  source : (bufferRegion s 113).HasBytes t.external bytes
  savedInput : (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi
  inputFlag : t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0)
  zeros : ∀ k, 120 ≤ k → k ≤ offset → t.external[stackPtr s - BitVec.ofNat 64 k]? = some 0

theorem zeroing_address (s : RamState) {offset i : Nat} (h : i ≤ offset) :
    stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
      stackPtr s - BitVec.ofNat 64 (offset - i) := by
  have he : offset = offset - i + i := by omega
  conv => lhs; rw [he]
  simp [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.neg_add,
    BitVec.add_assoc, BitVec.add_left_neg]

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem Zeroing.of_store (pre : CalleePre s boundary 0x110d70 72 65 328)
    {offset len : Nat} (h : Zeroing s t boundary bytes infinity (offset - len))
    (ho : offset ≤ 184) (hl : len + 119 ≤ offset) (hpos : 0 < len)
    {e : Effect} (step : Machine.step t = some (.next u)) (ready : ReadyToStep u)
    (effect : e.Holds t u)
    (components : e.components = [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip])
    (next : InProgram e.rip)
    (zero : ∀ i, i < len →
      u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? = some 0) :
    Zeroing s u boundary bytes infinity offset := by
  have agrees := effect.agrees
  rw [components] at agrees
  have writes : WritesWithin [.mem (stackPtr s - BitVec.ofNat 64 offset) len, .rip]
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨workRegion s 328, by simp, work_contains pre (by omega) (by omega) ha⟩
    · exact ha.elim
  obtain ⟨fuel, execution⟩ := h.execution
  have run := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program pre.outerBoundary next))
  refine ⟨h.state.after_effect pre (by decide) ready agrees writes (by simp),
    ⟨fuel + 1, execution.trans run⟩,
    (agrees.read (n := 64) (r := 5) (by simp)).trans h.destination, ?_, ?_, ?_, ?_⟩
  · exact hasBytes_agrees_apart agrees (by
      intro a n hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact stack_sub_apart pre.stack (by omega) (by decide) (by omega) (by decide)
        (.inl (by omega))) h.source
  · change memLoad u.external _ 64 = _
    rw [memLoad_agrees_apart agrees (by
      intro a n hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact stack_sub_apart pre.stack (b := 192) (nb := 8)
        (by omega) (by decide) (by omega) (by decide)
        (.inr (by omega)))]
    exact h.savedInput
  · rw [agrees.byte]
    · exact h.inputFlag
    · intro c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have hs := stack_contains pre (by omega) (by omega) ha
        have hi : (registerRegion s .rsi 72).Contains (s.regValue .rsi + 64).toNat := by
          exact memoryRegion_contains_add pre.inputBounded (len := 72)
            (Nat.le_refl _) (Nat.le_refl _) (i := 64) (by decide)
        exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hi hs
      · exact ha
  · intro k hk hko
    by_cases hkold : k ≤ offset - len
    · rw [agrees.byte]
      · exact h.zeros k hk hkold
      · intro c hc ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨i, hi, he⟩ := ha
          apply stack_sub_apart pre.stack (a := offset) (b := k) (na := len) (nb := 1)
            (by omega) (by omega) (by omega) (by omega) (.inl (by omega)) i hi 0 (by decide)
          simpa only [BitVec.add_zero] using he.symm
        · exact ha
    · have hz := zero (offset - k) (by omega)
      rw [zeroing_address s (by omega), Nat.sub_sub_self hko] at hz
      exact hz

theorem Zeroing.finish (h : Zeroing s t boundary bytes infinity 184) :
    Preparing s t boundary bytes infinity := by
  refine ⟨h.state, h.execution, h.destination, h.source, h.savedInput, h.inputFlag, rfl, ?_⟩
  intro i
  have hi : i.val < 65 := i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr s - 184).toNat + i.val)]? = _
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change t.external[stackPtr s - BitVec.ofNat 64 184 + BitVec.ofNat 64 i.val]? = _
  simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]
  rw [zeroing_address s (offset := 184) (i := i.val) (by omega)]
  exact h.zeros (184 - i.val) (by omega) (by omega)

end P256.Proofs.Sec1Serialize
