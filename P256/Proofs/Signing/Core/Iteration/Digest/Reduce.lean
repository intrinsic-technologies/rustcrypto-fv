import P256.Proofs.Signing.Core.Iteration.Digest.Copy
import P256.Proofs.Signing.Core.Iteration.Digest.Callee
import P256.Proofs.Verifying.Core.Reduce.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar

theorem reduce [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce z : Nat} (pre : SignPre s boundary)
    (input : NonceState s t state nonce) (value : Nat256At t (frameBase s+1328) z)
    (rip : t.RIP = 0x10cca1) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10ccf1 ∧
      NonceState s u state nonce ∧ Nat256At u (frameBase s+1296) (z % Operations.domain.n) := by
  obtain ⟨n,a,runA,frameA,effectA⟩ := Copy.run pre input.frame rip
  have preserved : Preserved s t a := by
    intro i hi
    unfold LiveOffset at hi
    apply word_writes_byte (Copy.writes input.frame) effectA.agrees (by omega)
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    constructor <;> omega
  have stateA := input.after_agrees frameA effectA.agrees preserved (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [Copy.Block.effect,Effect.components])
  have valueA : Nat256At a (frameBase s+528) z :=
    ⟨value.1,fun i hi => (Copy.copied pre input.frame frameA effectA i hi).trans (value.2 i hi)⟩
  have siA : a.regValue .rsi = frameBase s+528 := effectA.writes.2.2.1.trans input.rbp
  have diA : a.regValue .rdi = frameBase s+1296 :=
    effectA.writes.2.2.2.1.trans (congrArg (·+1296) input.frame.rsp)
  obtain ⟨v,runV,readyV,call⟩ := ScalarFrame.scalar_call pre.toCalleePre (by decide) (by decide)
    (NextNonce.scalarFrame frameA) 0xccec 0x642f (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x13120 (by decide)) effectA.rip
  change (callEffect (fun _ => 0x113120) 0x10ccf1 a).Holds a v at call
  have cp := local_call_pre pre frameA readyV call
    (inputBytes := 32) (outputBytes := 32) (reserve := 104)
    (inProgram_of_textOffset 0xccf1 (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) siA diA
  have siV : v.regValue .rsi = frameBase s+528 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans siA
  have diV : v.regValue .rdi = frameBase s+1296 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans diA
  have valueV : Nat256At v (v.regValue .rsi) z := by
    rw [siV]
    exact ⟨valueA.1,fun i hi => (local_call_copy frameA call (offset := 528) (len := 32)
      (by decide) i hi).trans (valueA.2 i hi)⟩
  obtain ⟨u,result,valueU⟩ := Verifying.Core.Reduce.reduce_correct cp valueV
  have stateU := stateA.after_result (output := 1296) pre readyV call result (by decide) (by decide) diA
    (by intro i hi; change i < 1296 ∨ 1328 ≤ i; unfold LiveOffset at hi; omega)
  obtain ⟨m,runU⟩ := result.execution
  exact ⟨n+1+m,u,(runA.trans runV).trans runU,result.rip.trans (callEffect_stack call).1,
    stateU,diV ▸ valueU⟩

end P256.Proofs.Signing.Core.Iteration.Digest
