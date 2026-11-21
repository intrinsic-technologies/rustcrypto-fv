import P256.Proofs.Verifying.Core.Scalars.InverseSetup
import P256.Proofs.Verifying.Core.Scalars.InverseCall
import P256.Proofs.Verifying.Core.Scalars.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar
open Standards.SECG.ECC

theorem invert [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d r scalarS : Nat}
    (core : Core.Inverse.CoreStage) (positive : 0 < scalarS) (bound : scalarS < Operations.domain.n)
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dc78)
    (pointers : Prepare.Pointers s t)
    (digest : Nat256At t (frameBase s+968) d)
    (savedR : Nat256At t (frameBase s+704) r)
    (savedS : Nat256At t (frameBase s+736) scalarS) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10dca0 ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s+128) (Curve.inverse Operations.domain.n scalarS) ∧
      Nat256At u (frameBase s+968) d ∧ Nat256At u (frameBase s+704) r ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,effectA,memoryA⟩ := inverse_setup pre state rip
  have keep {address : BitVec 64} {x : Nat} (h : Nat256At t address x) : Nat256At a address x :=
    ⟨h.1,fun i hi => by rw [memoryA];exact h.2 i hi⟩
  have pointersA := pointers.after effectA.agrees (by simp [inverseSetupEffect,Effect.components])
  have si : a.regValue .rsi = frameBase s+736 := by
    have h : a.regValue .rsi = stackPtr t+736 := effectA.writes.2
    rw [h,state.rsp]
    rfl
  have di : a.regValue .rdi = frameBase s+128 := by
    have h : a.regValue .rdi = stackPtr t+128 := effectA.writes.1
    rw [h,state.rsp]
    rfl
  obtain ⟨m,b,runB,stateB,ripB,pointersB,invB,flagB,bytesB,memoryB⟩ :=
    inverse_call core positive bound pre stateA effectA.rip si di pointersA (keep savedS)
  have digestB := call_slot bytesB (by decide) (Or.inl (by decide)) (keep digest)
  have rB := call_slot bytesB (by decide) (Or.inl (by decide)) (keep savedR)
  obtain ⟨u,runU,stateU,ripU,agreesU⟩ := inverse_guard pre stateB ripB flagB
  have pointersU := pointersB.after agreesU (by simp)
  have memoryU : MemoryWriteFrame b u (prefixRegions s) := agreesU.memoryWriteFrame (by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    have addr : frameBase s+0 = stackPtr s-1176 := by
      simp only [frameBase]
      exact BitVec.add_zero _
    rw [addr] at ha
    exact prefix_stack_contains pre (by decide) (by decide) ha)
  refine ⟨n+m+4,u,(runA.trans runB).trans runU,stateU,ripU,pointersU,
    guard_slot agreesU (by decide) (by decide) invB,
    guard_slot agreesU (by decide) (by decide) digestB,
    guard_slot agreesU (by decide) (by decide) rB,?_⟩
  intro address outside
  rw [memoryU address outside,memoryB address outside,memoryA]

end P256.Proofs.Verifying.Core.Scalars
