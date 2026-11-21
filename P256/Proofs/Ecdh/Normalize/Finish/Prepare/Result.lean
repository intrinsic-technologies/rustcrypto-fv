import P256.Proofs.Ecdh.Normalize.Finish.Prepare.Save
import P256.Proofs.Ecdh.Normalize.Finish.Prepare.Constants

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

set_option maxHeartbeats 600000 in
set_option maxRecDepth 2048 in
theorem prepare_saved [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Saved s t boundary point) : ∃ u, Prepared s u boundary point := by
  obtain ⟨n,b,runB,frameB,eB⟩ := constant_setup_correct pre state.toFrameState state.rip
  have spT : stackPtr t = frameBase s := state.rsp
  have spB : stackPtr b = frameBase s := frameB.rsp
  have dst : b.regValue .rdi = frameBase s + 248 := by
    have h : b.regValue .rdi = stackPtr t + 248 := eB.writes.2.2.2.1
    exact h.trans (congrArg (fun p => p+248) spT)
  have src : b.regValue .rsi = 0x2024f0 := eB.writes.2.2.2.2
  obtain ⟨u,runU,frameU,ripU,bytes,gU⟩ := movsq72 pre frameB 0x4b8 248
    (by decide) (by decide) (by decide +kernel) eB.rip
    (by rw [dst,spB]; rfl) eB.writes.2.2.1
    (by rw [src]; exact PublicPoint.Normalize.Finish.constant_readable frameB.loaded)
    (by rw [src,dst]
        have addr : frameBase s+248 = stackPtr s-1808 := by
          simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
        rw [addr]
        exact constant_disjoint pre)
  rw [src,dst] at bytes
  have preservedB (i : Nat) (hi : i < 65) :
      b.external[frameBase s+1016+BitVec.ofNat 64 i]? =
        t.external[frameBase s+1016+BitVec.ofNat 64 i]? := by
    apply eB.agrees.byte
    intro c hc ha
    simp only [constantSetupEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl)|rfl <;> try exact ha.elim
    change (Component.mem (stackPtr t+1088) 1).Covers _ at ha
    rw [spT] at ha
    obtain ⟨j,hj,he⟩ := ha
    exact RangeApart.offsets (frameBase s) (a := 1088) (b := 1016)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  have preserved (i : Nat) (hi : i < 65) :
      u.external[frameBase s+1016+BitVec.ofNat 64 i]? =
        t.external[frameBase s+1016+BitVec.ofNat 64 i]? := by
    apply Eq.trans _ (preservedB i hi)
    apply gU.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    rw [dst] at ha
    obtain ⟨j,hj,he⟩ := ha
    exact RangeApart.offsets (frameBase s) (a := 248) (b := 1016)
      (by decide) (by decide) (.inl (by decide)) j hj i hi he.symm
  have g := eB.agrees.trans gU
  have ax : stackPtr s - 1040 = frameBase s + 1016 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have ay : stackPtr s - 1008 = frameBase s + 1048 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have zx : stackPtr s - 1808 = frameBase s + 248 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd]
  have zy : stackPtr s - 1776 = frameBase s + 280 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd]
  refine ⟨u,frameU,?_,ripU,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try simp only [ax, ay, zx, zy]
  · obtain ⟨fuel,run⟩ := state.execution
    exact ⟨fuel+n+9,(run.trans runB).trans runU⟩
  · exact (g.read (n := 64) (r := 3) (by simp [constantSetupEffect,Effect.components])).trans state.output
  · exact state.x.of_bytes_eq (fun i hi => preserved i (by omega))
  · apply state.y.of_bytes_eq
    intro i hi
    have h := preserved (32+i) (by omega)
    rw [buffer_add s 1016 32 i] at h
    simp only [BitVec.reduceAdd] at h
    exact h
  · apply (PublicPoint.Normalize.Finish.constant_zero frameB.loaded 0 (by decide)).of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using bytes i (by omega)
  · apply (PublicPoint.Normalize.Finish.constant_zero frameB.loaded 32 (by decide)).of_bytes_eq
    intro i hi
    have h := bytes (32+i) (by omega)
    rw [buffer_add s 248 32 i] at h
    simp only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.reduceAdd] at h
    exact h
  · exact (g.read (n := 8) (r := 5) (by simp [constantSetupEffect,Effect.components])).trans state.choice
  · have h : b.regValue .rax = stackPtr t+248 := eB.writes.2.1
    exact (gU.read (n := 64) (r := 0) (by simp)).trans (h.trans (congrArg (fun p => p+248) spT))
  · exact (g.read (n := 64) (r := 2) (by simp [constantSetupEffect,Effect.components])).trans state.rdx

end P256.Proofs.Ecdh.Normalize.Finish
