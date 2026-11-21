import P256.Proofs.Verifying.Message.Convert.Context

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame_address (s : RamState) (offset : Nat) (bound : offset ≤ 1176) :
    frameBase s + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (1176-offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 1176 offset (by omega) bound]
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem preserved_bytes [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {offset len readOffset readLen : Nat} {cs : List Component}
    (pre : Pre initial boundary message) (state : Message.Frame initial s)
    (agrees : AgreesExcept cs s t)
    (bound : offset + len ≤ 1176) (readBound : readOffset + readLen ≤ 1176)
    (apart : offset + len ≤ readOffset ∨ readOffset + readLen ≤ offset)
    (covers : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    ∀ i < readLen,
      t.external[frameBase initial + BitVec.ofNat 64 readOffset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 readOffset + BitVec.ofNat 64 i]? := by
  intro i hi
  rw [frame_address initial readOffset (by omega)]
  apply agrees.byte
  intro c hc ha
  obtain ⟨j, hj, eq⟩ := covers c hc _ ha
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)] at eq
  exact stack_sub_apart pre.stack (by omega) (by omega) (by omega) (by omega)
    (by rcases apart with h | h <;> omega) j hj i hi eq.symm

theorem Context.after_write [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {fuel offset len : Nat} {cs : List Component}
    (pre : Pre initial boundary message) (state : Context initial s boundary message)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (bound : offset + len + 48 ≤ 1176)
    (apart : offset + len ≤ 384 ∨ 472 ≤ offset)
    (covers : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a)
    (sp : .reg 4 ∉ cs) (df : .df ∉ cs) (mxcsr : .mxcsr ∉ cs) (fcw : .fcw ∉ cs) :
    Context initial t boundary message := by
  have writes : WritesWithin cs #v[workRegion initial 9992] := by
    intro c hc a ha
    have covered := covers c hc a ha
    rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)] at covered
    exact ⟨workRegion initial 9992, by simp, work_contains pre.toCalleePre (by omega) (by omega) covered⟩
  have frame := state.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees
    (by
      intro c hc a ha
      obtain ⟨region, member, covered⟩ := writes c hc a ha
      exact ⟨region, by simpa using Or.inr member, covered⟩) sp df mxcsr fcw
  apply state.advance run frame (work_frame_stack pre.toCalleePre (agrees.memoryWriteFrame writes))
  intro i hi
  change t.external[frameBase initial + BitVec.ofNat 64 384 + BitVec.ofNat 64 i]? =
    s.external[frameBase initial + BitVec.ofNat 64 384 + BitVec.ofNat 64 i]?
  rw [frame_address initial 384 (by decide)]
  apply agrees.byte
  intro c hc ha
  obtain ⟨j, hj, eq⟩ := covers c hc _ ha
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)] at eq
  exact stack_sub_apart pre.stack (by omega) (by decide) (by omega) (by decide)
    (by rcases apart with h | h <;> omega) j hj i hi eq.symm

end P256.Proofs.Verifying.Message.Convert
