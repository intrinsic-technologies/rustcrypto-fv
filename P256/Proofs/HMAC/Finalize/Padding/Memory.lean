import P256.Proofs.HMAC.Finalize.Padding.Interface
import P256.Proofs.HMAC.Finalize.Call

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem scratch_contains [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    {offset len : Nat} {a : BitVec 64} (bound : offset ≤ 672) (high : len + 152 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (scratchRegion initial).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack bound
  rw [toNat_add_ofNat _ _ (by rw [low]; omega), low]
  change (stackPtr initial).toNat - 672 ≤ _ ∧
    _ < (stackPtr initial).toNat - 672 + 520
  constructor <;> omega

theorem scratch_frame {initial s t : RamState}
    (memory : MemoryWriteFrame s t #v[scratchRegion initial]) :
    MemoryWriteFrame s t
      #v[registerRegion initial .rdi 0, workRegion initial 672] := by
  intro a ha
  apply memory a
  intro region member inside
  have eq : region = scratchRegion initial := by simpa using member
  subst region
  apply ha (workRegion initial 672) (by simp)
  change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 672 + 520 at inside
  change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 672 + (672 - 48)
  exact ⟨inside.1, by omega⟩

theorem call_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (effect : (callEffect target ret s).Holds s t) :
    MemoryWriteFrame s t #v[scratchRegion initial] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a covered
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact covered.elim
  · rw [call_address state] at covered
    exact ⟨_, by simp, scratch_contains pre (by decide) (by decide) covered⟩
  · exact covered.elim

theorem call_byte [Bindings] {initial s t : RamState}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (effect : (callEffect target ret s).Holds s t)
    {offset len : Nat} (ho : offset ≤ 328) (hl : len ≤ offset + 8) {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    rw [call_address state] at he
    have ha : stackPtr initial - BitVec.ofNat 64 offset =
        (stackPtr initial - 336) + BitVec.ofNat 64 (336-offset) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 336 offset (by omega) (by omega)]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(336 : BitVec 64)),
        show -(336 : BitVec 64) + 336#64 = 0#64 by decide +kernel, BitVec.zero_add]
    apply RangeApart.offsets (stackPtr initial - 336) (a := 0) (b := 336-offset)
      (len := 8) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
    rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
    exact he.symm
  · exact hv.elim

end P256.Proofs.HMAC.Finalize.Padding
