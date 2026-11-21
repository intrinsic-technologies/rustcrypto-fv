import P256.Proofs.Signing.Core.Iteration.Digest.Callee
import P256.Proofs.Signing.Core.Iteration.Digest.Invert.Guard
import P256.Proofs.Signing.Core.Iteration.Digest.Invert.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Invert

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program SecretKeyFromBytes.Scalar Standards.SECG.ECC

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce z : Nat} (pre : SignPre s boundary)
    (input : NonceState s t state nonce) (digest : Nat256At t (frameBase s+1296) z)
    (inverse : Nat256At t (frameBase s+528) (Curve.inverse Operations.domain.n nonce))
    (rbx : t.regValue .rbx = frameBase s+304)
    (flag : t.external[frameBase s+560]? = some 1) (rip : t.RIP = 0x10cd04) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cd5b ∧
      NonceState s u state nonce ∧ Nat256At u (frameBase s+1296) z ∧
      Nat256At u (frameBase s+336) (Curve.inverse Operations.domain.n nonce) ∧ u.regValue .rbx = frameBase s+304 := by
  obtain ⟨a,runA,frameA,ripA,agreesA⟩ := inverse_guard pre input.frame rip flag
  have writesA : WordWrites (frameBase s) [1328]
      [.reg 0,.mem (frameBase s+1328) 1,.flags,.rip] := by
    intro c hc address cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    all_goals try exact cover.elim
    obtain ⟨i,hi,rfl⟩ := cover
    exact ⟨1328,by simp,i,by omega,rfl⟩
  have memoryA (i : Nat) (hi : i < 2280) (apart : i < 1328 ∨ 1336 ≤ i) :
      a.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]? := by
    apply word_writes_byte writesA agreesA (by omega)
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    subst off
    exact ⟨by decide,apart⟩
  have stateA := input.after_agrees frameA agreesA
    (by intro i hi; unfold LiveOffset at hi; exact memoryA i (by omega) (by omega))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> simp)
  have inverseA : Nat256At a (frameBase s+528) (Curve.inverse Operations.domain.n nonce) := by
    refine ⟨inverse.1,fun i hi => ?_⟩
    have h := memoryA (528+i) (by omega) (.inl (by omega))
    rw [BitVec.ofNat_add,← BitVec.add_assoc] at h
    exact h.trans (inverse.2 i hi)
  obtain ⟨n,u,runU,frameU,effectU⟩ := Copy.run pre frameA ripA
  have memoryU (i : Nat) (hi : i < 2280) (apart : i < 336 ∨ 368 ≤ i) :
      u.external[frameBase s+BitVec.ofNat 64 i]? = a.external[frameBase s+BitVec.ofNat 64 i]? := by
    apply word_writes_byte (Copy.writes frameA) effectU.agrees (by omega)
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    constructor <;> omega
  have stateU := stateA.after_agrees frameU effectU.agrees
    (by intro i hi; unfold LiveOffset at hi; exact memoryU i (by omega) (by omega))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> simp [Copy.Block.effect,Effect.components])
  have digestU : Nat256At u (frameBase s+1296) z := by
    refine ⟨digest.1,fun i hi => ?_⟩
    have h := (memoryU (1296+i) (by omega) (.inr (by omega))).trans
      (memoryA (1296+i) (by omega) (.inl (by omega)))
    rw [BitVec.ofNat_add,← BitVec.add_assoc] at h
    exact h.trans (digest.2 i hi)
  exact ⟨4+n,u,runA.trans runU,effectU.rip,stateU,digestU,
    ⟨inverseA.1,fun i hi => (Copy.copied pre frameA frameU effectU i hi).trans (inverseA.2 i hi)⟩,
    (effectU.agrees.read (n := 64) (r := 3) (by simp [Copy.Block.effect,Effect.components])).trans
      ((agreesA.read (n := 64) (r := 3) (by simp)).trans rbx)⟩

end P256.Proofs.Signing.Core.Iteration.Digest.Invert
