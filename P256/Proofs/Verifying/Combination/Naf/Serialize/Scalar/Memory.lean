import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Memory [Bindings] (s t : RamState) (cursor point : BitVec 64) : Prop
    extends FrameState s t cursor where
  cursorValue : memLoad t.external cursor 64 = point + 128

theorem Memory.registers [Bindings] {s t u : RamState} {cursor point : BitVec 64} {cs : List Component}
    (state : Memory s t cursor point) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hsp : .reg 4 ∉ cs)
    (hbp : .reg 5 ∉ cs) (h12 : .reg 12 ∉ cs) (h13 : .reg 13 ∉ cs) (h15 : .reg 15 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Memory s u cursor point := by
  refine ⟨state.toFrameState.after_registers ready agrees hm hsp hbp h12 h13 h15, ?_⟩
  change memLoad u.external _ 64 = _
  rw [agrees.external hm]
  exact state.cursorValue

theorem input_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {so : BitVec 64} (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor so)
    {i : Nat} (hi : i < 128) :
    t.external[point + BitVec.ofNat 64 i]? =
      s.external[point + BitVec.ofNat 64 i]? := by
  have hb : (point).toNat + 128 < 2^32 := pre.pointBounded
  have hin : (pairRegion point).Contains (point + BitVec.ofNat 64 i).toNat := by
    change (point).toNat ≤ _ ∧ _ < (point).toNat + 128
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  apply state.frame
  intro region hr ha
  have hr' : region = registerRegion s .rdi 272 ∨ region = cursorRegion cursor ∨ region = Stack.region s 536 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · exact pre.pointOutput _ hin ha
  · exact pre.cursorApart _ (by simp) _ ha hin
  · exact pre.pointStack _ hin ha

theorem input_at [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {so : BitVec 64} {n : Nat}
    (pre : ScalarPre s boundary cursor point) (state : FrameState s t cursor so)
    (input : Nat256At s (point + 96) n) : Nat256At t (point + 96) n := by
  refine ⟨input.1, ?_⟩
  intro i hi
  have h := input_byte pre state (i := 96+i) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
  exact h.trans (input.2 i hi)

theorem cursor_read_of_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 272, Stack.region s 536]) :
    memLoad u.external cursor 64 = memLoad t.external cursor 64 := by
  apply memLoad_congr
  intro i hi
  have hb : cursor.toNat + 8 < 2^32 := pre.cursorBounded
  have hin : (cursorRegion cursor).Contains (cursor + BitVec.ofNat 64 i).toNat := by
    change cursor.toNat ≤ _ ∧ _ < cursor.toNat + 8
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  change (u.external[cursor + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[cursor + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr ha
  have hr' : region = registerRegion s .rdi 272 ∨ region = Stack.region s 536 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.cursorApart _ (by simp) _ hin ha
  · exact pre.cursorApart _ (by simp) _ hin ha


end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
