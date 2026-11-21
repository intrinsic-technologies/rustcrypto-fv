import Hkdf.Proofs.Common.SHA256.Entry.Frame
import Hkdf.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Encoding.Serialize

variable [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt32} {input : ByteArray} {count : Nat}

theorem FrameState.stackOffset_toNat (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset : Nat} (ho : offset ≤ 288) :
    (stackPtr current + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - 336 + offset := by
  have sub : (stackPtr initial - 336).toNat = (stackPtr initial).toNat - 336 :=
    stack_sub_toNat pre.toCalleePre (offset := 336) (by decide)
  rw [state.rsp, BitVec.toNat_add, sub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt]
  have bound := stack_bounds pre.toCalleePre
  omega

theorem FrameState.stackOffset_contains (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset : Nat} (ho : offset < 288) :
    (Stack.region initial 336).Contains (stackPtr current + BitVec.ofNat 64 offset).toNat := by
  change (stackPtr initial).toNat - 336 ≤ _ ∧ _ <
    (Stack.region initial 336).start + (Stack.region initial 336).size
  rw [stack_region_end, state.stackOffset_toNat pre (by omega)]
  have bound := stack_bounds pre.toCalleePre
  constructor <;> omega

theorem FrameState.stackOffset_local (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset len : Nat} (ho : offset + len ≤ 288)
    {a : BitVec 64} (ha : (Component.mem (stackPtr current + BitVec.ofNat 64 offset) len).Covers a) :
    LocalWrite initial a := by
  obtain ⟨i, hi, rfl⟩ := ha
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  right
  rw [state.stackOffset_toNat pre (by omega)]
  have bound := stack_bounds pre.toCalleePre
  constructor <;> omega

theorem FrameState.stackOffset_readable (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset len : Nat} (ho : offset + len ≤ 288) :
    MemReadable current (stackPtr current + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow _ state.allocated
  apply memoryRegion_memReadable pre.stack.1 pre.stack.2.1
  · rw [state.stackOffset_toNat pre (by omega)]
    exact Nat.le_add_right _ _
  · rw [state.stackOffset_toNat pre (by omega), stack_region_end]
    have bound := stack_bounds pre.toCalleePre
    omega

theorem FrameState.stack_tables (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) :
    (stackPtr current).toNat + 288 ≤ 0x1000 ∨ 0x3000 ≤ (stackPtr current).toNat := by
  have hs : (stackPtr current).toNat = (stackPtr initial).toNat - 336 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] using
      state.stackOffset_toNat pre (offset := 0) (by decide)
  have bounds := stack_bounds pre.toCalleePre
  apply Classical.byContradiction
  intro h
  let a := max (stackPtr current).toNat 0x1000
  have ha : (stackPtr current).toNat ≤ a ∧ a < (stackPtr current).toNat + 288 ∧
      0x1000 ≤ a ∧ a < 0x3000 := by dsimp only [a]; omega
  have hlow : a < 2^64 := by omega
  apply pre.avoids (Stack.region initial 336) (by simp) (BitVec.ofNat 64 a)
  · change (stackPtr initial).toNat - 336 ≤ _ ∧
      _ < (Stack.region initial 336).start + (Stack.region initial 336).size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlow, stack_region_end]
    omega
  · right
    change 0x1000 ≤ (BitVec.ofNat 64 a).toNat ∧ (BitVec.ofNat 64 a).toNat < 0x1000 + 0x2000
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlow]
    omega

theorem FrameState.stackOffset_writable (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset len : Nat} (ho : offset + len ≤ 288) :
    Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable current
      (stackPtr current + BitVec.ofNat 64 offset) len := by
  refine ⟨state.stackOffset_readable pre ho, ?_⟩
  have tables := state.stack_tables pre
  have hs := state.stackOffset_toNat pre (offset := 0) (by decide)
  simp only [BitVec.add_zero, Nat.add_zero] at hs
  rw [state.stackOffset_toNat pre (by omega)]
  omega

theorem FrameState.stackOffset_codeApart (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset len pos codeLen : Nat}
    (ho : offset + len ≤ 288)
    (hc : ∀ j < codeLen, InProgram (BitVec.ofNat 64 (0x100000 + pos) + BitVec.ofNat 64 j)) :
    RangeApart (stackPtr current + BitVec.ofNat 64 offset) len
      (BitVec.ofNat 64 (0x100000 + pos)) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region initial 336) (by simp)
    (stackPtr current + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.stackOffset_contains pre (by omega)
  · exact Or.inl (he.symm ▸ hc j hj)

theorem FrameState.hashWord_readable (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {i : Nat} (hi : i < 8) :
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

theorem FrameState.stackOffset_hashApart (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial current) {offset len i : Nat} (ho : offset + len ≤ 288)
    (hi : i < 8) :
    RangeApart (stackPtr current + BitVec.ofNat 64 offset) len
      (initial.regValue .rdi + BitVec.ofNat 64 (4*i)) 4 := by
  intro j hj k hk he
  have hstack : (Stack.region initial 336).Contains
      (stackPtr current + BitVec.ofNat 64 offset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact state.stackOffset_contains pre (by omega)
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hstack
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (by change 4*i+k<32; omega)

end Hkdf.Proofs.Common.SHA256
