import P256.Proofs.Nonce.Fill.Work

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {state : State}

theorem stack_component (pre : Pre initial boundary orderAddress state) (frame : Frame initial s)
    {off len : Nat} (bound : off + len ≤ 184) {a : BitVec 64}
    (covered : (Component.mem (stackPtr s + BitVec.ofNat 64 off) len).Covers a) :
    (ScalarFrame.workRegion initial 2096).Contains a.toNat := by
  rw [frame.rsp, frameBase_add initial (by omega)] at covered
  exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) covered

theorem stack_frame {t : RamState} {components : List Component}
    (pre : Pre initial boundary orderAddress state) (frame : Frame initial s)
    (agrees : AgreesExcept components s t)
    (shape : ∀ c ∈ components, ∀ a, c.Covers a →
      ∃ off len : Nat, off + len ≤ 184 ∧ (Component.mem (stackPtr s + BitVec.ofNat 64 off) len).Covers a) :
    MemoryWriteFrame s t #v[Stack.region initial 2096] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  obtain ⟨off, len, bound, covered⟩ := shape c hc a ha
  exact ⟨_, by simp, work_substack pre (stack_component pre frame bound covered)⟩

end P256.Proofs.Nonce.Fill.Entry
