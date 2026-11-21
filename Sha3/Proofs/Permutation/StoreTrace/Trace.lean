import Sha3.Proofs.Permutation.StoreTrace.Relation
import Sha3.Proofs.Permutation.StoreTrace.Finish

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure PrefixInvariant (copy : Copy) (sp pointer : BitVec 64) (initial : RamState)
    (i : Fin 42) (s : RamState) : Prop where
  memory : Memory copy sp pointer s
  rip : s.RIP = dataPc copy i
  model : Models sp pointer (runPrefix (model sp pointer initial) i.val) s
  frame : AgreesExcept (Store.effect copy sp pointer initial).components initial s

theorem dataPc_ne_boundary {copy : Copy} {boundary : ReturnBoundary}
    (hb : ∀ p : BitVec 64, (storeAddress copy).toNat ≤ p.toNat →
      p.toNat ≤ (Store.restoreAddress copy).toNat → p ≠ boundary.rip)
    (i : Fin 42) : dataPc copy i ≠ boundary.rip := by
  have h := pc_bounds copy i
  exact hb _ h.1 h.2

theorem traceStep_advance [Bindings] {copy : Copy} {boundary : ReturnBoundary}
    {sp pointer : BitVec 64}
    {initial : RamState} (hp : Store.Pre copy sp pointer initial)
    (hb : ∀ p : BitVec 64, (storeAddress copy).toNat ≤ p.toNat →
      p.toNat ≤ (Store.restoreAddress copy).toNat → p ≠ boundary.rip)
    (i : Fin 41)
    (hs : TraceStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i) (dataBytes i)) :
    AdvanceTriple boundary 1 (PrefixInvariant copy sp pointer initial i.castSucc)
      (codeRange (storeAddress copy) Store.bytes)
      (fun _ t ↦ PrefixInvariant copy sp pointer initial i.succ t) := by
  intro s hready hcode hi
  have hpre : StepPre copy sp pointer (dataPc copy i.castSucc) (dataOp i) s :=
    ⟨hi.rip, models_stack hp i.castSucc hi.model, pointerPre_prefix hp i hi.model, hi.memory⟩
  obtain ⟨t, hstep, hready', he⟩ :=
    hs sp pointer s hready (hcode.mono (code_subset copy i)) hpre
  have hne : t.RIP ≠ boundary.rip := by
    rw [he.rip]
    exact dataPc_ne_boundary hb i.succ
  refine ⟨t, Advances.of_step hstep (.inl hne), hready',
    he.codeIn (moveEffect_avoids (dataOp_allowed i) hi.memory) hcode, ?_⟩
  refine ⟨hi.memory.of_holds he, he.rip, ?_, moveEffect_frame (dataOp_allowed i) he hi.frame⟩
  change Models _ _ (runPrefix _ (i.val + 1)) t
  rw [runPrefix_succ]
  exact models_execute hi.model (dataOp_allowed i) hi.memory.apart he

theorem prefix_advance [Bindings] {copy : Copy} {boundary : ReturnBoundary} {sp pointer : BitVec 64}
    {initial : RamState} (hp : Store.Pre copy sp pointer initial)
    (hb : ∀ p : BitVec 64, (storeAddress copy).toNat ≤ p.toNat →
      p.toNat ≤ (Store.restoreAddress copy).toNat → p ≠ boundary.rip)
    (steps : ∀ i : Fin 41,
      TraceStep copy (dataPc copy i.castSucc) (dataPc copy i.succ) (dataOp i) (dataBytes i))
    (k : Fin 42) :
    AdvanceTriple boundary k.val (PrefixInvariant copy sp pointer initial 0)
      (codeRange (storeAddress copy) Store.bytes)
      (fun _ t ↦ PrefixInvariant copy sp pointer initial k t) := by
  induction k using Fin.induction with
  | zero =>
    intro s hready hcode hi
    exact ⟨s, (advances_zero boundary s s).mpr rfl, hready, hcode, hi⟩
  | succ i ih =>
    have hs := traceStep_advance hp hb i (steps i)
    exact (ih.seq hs (fun _ _ _ hi ↦ hi)).conseq (fun _ hi ↦ hi)
      (fun _ _ _ ⟨_, _, hi⟩ ↦ hi)

theorem prefixInvariant_initial {copy : Copy} {sp pointer : BitVec 64} {s : RamState}
    (hp : Store.Pre copy sp pointer s) : PrefixInvariant copy sp pointer s 0 s := by
  refine ⟨⟨hp.frameRead, hp.outputRead, hp.apart, hp.codeApart, hp.tables⟩, ?_, ?_,
    AgreesExcept.refl _ s⟩
  · exact hp.rip
  · change Models _ _ (runPrefix _ 0) s
    rw [runPrefix_zero]
    exact fun _ ↦ rfl

theorem prefixInvariant_final_rip {copy : Copy} {sp pointer : BitVec 64} {initial s : RamState}
    (h : PrefixInvariant copy sp pointer initial ⟨41, by decide⟩ s) :
    s.RIP = Store.restoreAddress copy := h.rip

end Sha3.Proofs.Permutation.StoreTrace
