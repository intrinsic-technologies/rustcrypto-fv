import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State
import P256.Proofs.Verifying.Combination.PointMemory
import P256.Proofs.Projective.Preserve
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Proofs.Projective P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem data_of_frame [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left) (frame : State s w)
    (regs : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r15], w.regValue r = t.regValue r)
    (bytes : ∀ off len : Nat, (off = 336 ∧ len = 96) ∨
      (off ∈ [400, 384, 392, 376] ∧ len = 8) → ∀ j < len,
      w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 j]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 j]?) :
    DigitData s w tables digits p q u v k point left := by
  have loads (off : Nat) (h : off ∈ [400, 384, 392, 376]) :
      memLoad w.external (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (bytes off 8 (.inr ⟨h, rfl⟩) i hi)
  exact ⟨⟨state.toMemory.of_frame pre frame,
      (regs .rbx (by simp)).trans state.count, state.positive, state.bounded,
      (regs .r15 (by simp)).trans state.scratch,
      state.value.of_bytes_eq (bytes 336 96 (.inl ⟨rfl,rfl⟩)),
      (loads 400 (by simp)).trans state.total,
      (loads 384 (by simp)).trans state.tableBase,
      (loads 392 (by simp)).trans state.output⟩,
    (regs .r13 (by simp)).trans state.cursor,
    (regs .rbp (by simp)).trans state.tableCursor,
    (regs .r12 (by simp)).trans state.remaining,
    (loads 376 (by simp)).trans state.savedCursor⟩

theorem stack_byte [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {cs : List Component} {destination size off len i : Nat}
    (pre : MultiPre s boundary tables digits) (agrees : AgreesExcept cs t w)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 destination) size).Covers a)
    (hd : destination ≤ 408) (hs : size ≤ destination + 8)
    (ho : off ≤ 408) (hl : len ≤ off + 8)
    (apart : off + size ≤ destination ∨ destination + len ≤ off) (hi : i < len) :
    w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  obtain ⟨j, hj, he⟩ := writes c hc _ ha
  exact stack_sub_apart pre.stack (by omega) (by omega) hs hl apart j hj i hi he.symm

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
