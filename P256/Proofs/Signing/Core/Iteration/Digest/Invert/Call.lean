import P256.Proofs.Signing.Core.Iteration.Digest.Invert.Setup
import P256.Proofs.Scalar.Inverse.Wrapper.Contract

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Invert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar Standards.SECG.ECC

theorem call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce z : Nat} (pre : SignPre s boundary)
    (input : NonceState s t state nonce) (digest : Nat256At t (frameBase s+1296) z)
    (rip : t.RIP = 0x10ccf1) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cd04 ∧
      NonceState s u state nonce ∧ Nat256At u (frameBase s+1296) z ∧
      Nat256At u (frameBase s+528) (Curve.inverse Operations.domain.n nonce) ∧
      u.external[frameBase s+560]? = some 1 ∧ u.regValue .rbx = frameBase s+304 := by
  obtain ⟨a,runA,frameA,effectA⟩ := setup pre input.frame rip
  have memoryA := effectA.agrees.external (by simp [setupEffect,Effect.components,Component.Covers])
  have stateA := input.after_agrees frameA effectA.agrees (fun _ _ => congrArg (·[_]?) memoryA)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> simp [setupEffect,Effect.components])
  have diA : a.regValue .rdi = frameBase s+528 := effectA.writes.1.trans input.rbp
  have siA : a.regValue .rsi = frameBase s+304 :=
    effectA.writes.2.1.trans (congrArg (·+304) input.frame.rsp)
  obtain ⟨v,runV,readyV,call⟩ := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide)
    (NextNonce.scalarFrame frameA) 0xccff 0x612c (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x12e30 (by decide)) effectA.rip
  change (callEffect (fun _ => 0x112e30) 0x10cd04 a).Holds a v at call
  have cp := local_call_pre pre frameA readyV call
    (inputBytes := 32) (outputBytes := 40) (reserve := 768)
    (inProgram_of_textOffset 0xcd04 (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) siA diA
  have siV : v.regValue .rsi = frameBase s+304 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans siA
  have diV : v.regValue .rdi = frameBase s+528 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans diA
  have valueV : Nat256At v (v.regValue .rsi) nonce := by
    rw [siV]
    exact ⟨stateA.scalar.1,fun i hi => (local_call_copy frameA call (offset := 304) (len := 32)
      (by decide) i hi).trans (stateA.scalar.2 i hi)⟩
  obtain ⟨u,result,valueU,flagU⟩ := Scalar.Inverse.Wrapper.nonzero_correct cp valueV input.positive input.canonical
  have stateU := stateA.after_result (output := 528) pre readyV call result (by decide) (by decide) diA
    (by intro i hi; change i < 528 ∨ 568 ≤ i; unfold LiveOffset at hi; omega)
  have digestU : Nat256At u (frameBase s+1296) z := by
    refine ⟨digest.1,fun i hi => ?_⟩
    change u.external[frameBase s+1296#64+BitVec.ofNat 64 i]? = _
    rw [local_result_copy pre frameA call result diA (offset := 1296) (len := 32)
      (by decide) (by decide) (.inr (by decide)) i hi,memoryA]
    exact digest.2 i hi
  obtain ⟨m,runU⟩ := result.execution
  refine ⟨3+1+m,u,(runA.trans runV).trans runU,result.rip.trans (callEffect_stack call).1,
    stateU,digestU,diV ▸ valueU,?_,?_⟩
  · change u.external[frameBase s+560#64]? = some 1
    simpa only [diV,BitVec.add_assoc,BitVec.reduceAdd] using flagU

  · exact (result.calleeSaved .rbx (by simp)).trans
      ((call.agrees.read (n := 64) (r := 3) (by simp)).trans
        (effectA.writes.2.2.trans (congrArg (·+304) input.frame.rsp)))

end P256.Proofs.Signing.Core.Iteration.Digest.Invert
