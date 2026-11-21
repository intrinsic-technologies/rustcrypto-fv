import P256.Proofs.SHA256.Entry.Frame
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

variable [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt32} {input : ByteArray} {count : Nat}

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_toNat (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset : Nat} (ho : offset ≤ 288) :
    (stackPtr current + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - 336 + offset := by
  have sub : (stackPtr initial - 336).toNat = (stackPtr initial).toNat - 336 :=
    stack_sub_toNat pre.stack (offset := 336) (by decide)
  rw [state.rsp, BitVec.toNat_add, sub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt]
  have bound := stack_bounds pre.stack
  omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_contains (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset : Nat} (ho : offset < 288) :
    (Stack.region initial 336).Contains (stackPtr current + BitVec.ofNat 64 offset).toNat := by
  change (stackPtr initial).toNat - 336 ≤ _ ∧ _ <
    (Stack.region initial 336).start + (Stack.region initial 336).size
  rw [stack_region_end, state.sha_stackOffset_toNat pre (by omega)]
  have bound := stack_bounds pre.stack
  constructor <;> omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_local (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset len : Nat} (ho : offset + len ≤ 288)
    {a : BitVec 64} (ha : (Component.mem (stackPtr current + BitVec.ofNat 64 offset) len).Covers a) :
    LocalWrite initial a := by
  obtain ⟨i, hi, rfl⟩ := ha
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  right
  rw [state.sha_stackOffset_toNat pre (by omega)]
  have bound := stack_bounds pre.stack
  constructor <;> omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_readable (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset len : Nat} (ho : offset + len ≤ 288) :
    MemReadable current (stackPtr current + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow _ state.allocated
  apply memoryRegion_memReadable pre.stack.1 pre.stack.2.1
  · rw [state.sha_stackOffset_toNat pre (by omega)]
    exact Nat.le_add_right _ _
  · rw [state.sha_stackOffset_toNat pre (by omega), stack_region_end]
    have bound := stack_bounds pre.stack
    omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_writable (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset len : Nat} (ho : offset + len ≤ 288) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable current
      (stackPtr current + BitVec.ofNat 64 offset) len := by
  have whole := state.sha_stackOffset_readable pre (offset := 0) (len := 288) (by decide)
  have tables : PageTableEntriesApart (stackPtr current).toNat 288 := by
    apply tables_of_not_reserved (by decide) (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using whole.low)
    intro i hi ht
    exact pre.avoids _ (by simp) _ (state.sha_stackOffset_contains pre hi) (.inr ht)
  refine ⟨state.sha_stackOffset_readable pre ho, ?_⟩
  have addr := state.sha_stackOffset_toNat pre (by omega : offset ≤ 288)
  have base := state.sha_stackOffset_toNat pre (offset := 0) (by decide)
  simp only [BitVec.add_zero, Nat.add_zero] at base
  rw [addr]
  unfold PageTableEntriesApart at tables ⊢
  omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_codeApart (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset len pos codeLen : Nat}
    (ho : offset + len ≤ 288)
    (hc : ∀ j < codeLen, InProgram (BitVec.ofNat 64 (0x100000 + pos) + BitVec.ofNat 64 j)) :
    RangeApart (stackPtr current + BitVec.ofNat 64 offset) len
      (BitVec.ofNat 64 (0x100000 + pos)) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region initial 336) (by simp)
    (stackPtr current + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.sha_stackOffset_contains pre (by omega)
  · exact Or.inl (he.symm ▸ hc j hj)

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_hashWord_readable (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {i : Nat} (hi : i < 8) :
    MemReadable current (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 4 := by
  apply readable_of_grow _ state.allocated
  apply memoryRegion_memReadable pre.outputBounded pre.outputAllocated
  all_goals
    have bound : (initial.regValue .rdi).toNat + 32 < 2^32 := pre.outputBounded
    have address : (initial.regValue .rdi + BitVec.ofNat 64 (4*i)).toNat =
        (initial.regValue .rdi).toNat + 4*i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [address]
    dsimp only [registerRegion]
    omega

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_stackOffset_hashApart (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial current 32 336 336) {offset len i : Nat} (ho : offset + len ≤ 288)
    (hi : i < 8) :
    RangeApart (stackPtr current + BitVec.ofNat 64 offset) len
      (initial.regValue .rdi + BitVec.ofNat 64 (4*i)) 4 := by
  intro j hj k hk he
  have hstack : (Stack.region initial 336).Contains
      (stackPtr current + BitVec.ofNat 64 offset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.sha_stackOffset_contains pre (by omega)
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hstack
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (by change 4*i+k<32; omega)

end P256.Proofs.SHA256
