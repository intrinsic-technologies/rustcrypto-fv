import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Copy
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem stack_bytes_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {writeOffset writeLen offset len : Nat}
    (pre : Pre s boundary) (frame : AgreesExcept cs t u)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 writeOffset) writeLen).Covers a)
    (hw : writeOffset ≤ 1400) (hwl : writeLen ≤ writeOffset+8)
    (ho : offset ≤ 1400) (hl : len ≤ offset+8)
    (apart : writeOffset + len ≤ offset ∨ offset + writeLen ≤ writeOffset)
    {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply frame.byte
  intro c hc ha
  obtain ⟨j, hj, eq⟩ := writes c hc _ ha
  exact stack_sub_apart pre.stack hw ho hwl hl apart.symm j hj i hi eq.symm

theorem stack_read_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {writeOffset writeLen offset n : Nat}
    (pre : Pre s boundary) (frame : AgreesExcept cs t u)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 writeOffset) writeLen).Covers a)
    (hw : writeOffset ≤ 1400) (hwl : writeLen ≤ writeOffset+8)
    (ho : offset ≤ 1400) (hl : n/8 ≤ offset+8)
    (apart : writeOffset + n/8 ≤ offset ∨ offset + writeLen ≤ writeOffset) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [stack_bytes_of_agrees pre frame writes hw hwl ho hl apart hi]

theorem after_single_write [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {writeOffset writeLen : Nat}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (ready : ReadyToStep u) (frame : AgreesExcept cs t u)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 writeOffset) writeLen).Covers a)
    (hw : writeOffset ≤ 1400) (hwl : writeLen+48 ≤ writeOffset) (sp : .reg 4 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    FrameState s u 96 1400 376 := by
  apply FrameState.after_effect pre.toCalleePre (by decide) state ready frame ?_ sp
  intro c hc a ha
  exact ⟨workRegion s 1400, by simp, work_contains pre.toCalleePre hw hwl (writes c hc a ha)⟩

theorem PointCallResult.trans [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}
    {ret₁ ret₂ : BitVec 64} {outputOffset : Nat} {point₁ point₂ : Projective}
    (left : PointCallResult s t u boundary ret₁ outputOffset point₁)
    (right : PointCallResult s u v boundary ret₂ outputOffset point₂) :
    PointCallResult s t v boundary ret₂ outputOffset point₂ := by
  refine ⟨right.toFrameState, ?_, right.rip, right.value, ?_, ?_⟩
  · obtain ⟨fuel₁, run₁⟩ := left.execution
    obtain ⟨fuel₂, run₂⟩ := right.execution
    exact ⟨fuel₁+fuel₂, run₁.trans run₂⟩
  · intro r hr
    exact (right.registers r hr).trans (left.registers r hr)
  · intro offset len ho hl apart i hi
    exact (right.bytes offset len ho hl apart i hi).trans (left.bytes offset len ho hl apart i hi)

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
