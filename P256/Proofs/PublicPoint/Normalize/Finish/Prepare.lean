import P256.Proofs.PublicPoint.Normalize.Finish.Save
import P256.Proofs.PublicPoint.Normalize.Finish.Constants

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

set_option maxHeartbeats 600000 in
set_option maxRecDepth 2048 in
theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Saved s t boundary point) : ∃ u, Prepared s u boundary point := by
  obtain ⟨n,b,runB,frameB,eB⟩ := constant_setup_correct pre state.toFrameState state.rip
  have spT : stackPtr t = frameBase s := state.rsp
  have spB : stackPtr b = frameBase s := frameB.rsp
  have dst : b.regValue .rdi = frameBase s + 1032 := by
    have h : b.regValue .rdi = stackPtr t + 1032 := eB.writes.2.2.2.1
    exact h.trans (congrArg (fun p => p+1032) spT)
  have src : b.regValue .rsi = 0x2024f0 := eB.writes.2.2.2.2
  obtain ⟨u,runU,frameU,ripU,bytes,gU⟩ := movsq72 pre frameB 0xeab6 1032
    (by decide) (by decide) (by decide +kernel) eB.rip
    (by rw [dst,spB]; rfl) eB.writes.2.2.1
    (by rw [src]; exact constant_readable frameB.loaded)
    (by rw [src,dst]
        have addr : frameBase s+1032 = stackPtr s-912 := by
          simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
        rw [addr]
        exact constant_disjoint pre)
  rw [src,dst] at bytes
  have preservedB (i : Nat) (hi : i < 65) :
      b.external[frameBase s+264+BitVec.ofNat 64 i]? =
        t.external[frameBase s+264+BitVec.ofNat 64 i]? := by
    apply eB.agrees.byte
    intro c hc ha
    simp only [constantSetupEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl)|rfl <;> try exact ha.elim
    change (Component.mem (stackPtr t+336) 1).Covers _ at ha
    rw [spT] at ha
    obtain ⟨j,hj,he⟩ := ha
    exact RangeApart.offsets (frameBase s) (a := 336) (b := 264)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  have preserved (i : Nat) (hi : i < 65) :
      u.external[frameBase s+264+BitVec.ofNat 64 i]? =
        t.external[frameBase s+264+BitVec.ofNat 64 i]? := by
    apply Eq.trans _ (preservedB i hi)
    apply gU.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    rw [dst] at ha
    obtain ⟨j,hj,he⟩ := ha
    exact RangeApart.offsets (frameBase s) (a := 1032) (b := 264)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  have g := eB.agrees.trans gU
  refine ⟨u,frameU,?_,ripU,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨fuel,run⟩ := state.execution
    exact ⟨fuel+n+9,(run.trans runB).trans runU⟩
  · exact (g.read (n := 64) (r := 3) (by simp [constantSetupEffect,Effect.components])).trans state.output
  · exact state.x.of_bytes_eq (fun i hi => preserved i (by omega))
  · apply state.y.of_bytes_eq
    intro i hi
    have h := preserved (32+i) (by omega)
    rw [buffer_add s 264 32 i] at h
    simp only [BitVec.reduceAdd] at h
    exact h
  · apply (constant_zero frameB.loaded 0 (by decide)).of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using bytes i (by omega)
  · apply (constant_zero frameB.loaded 32 (by decide)).of_bytes_eq
    intro i hi
    have h := bytes (32+i) (by omega)
    rw [buffer_add s 1032 32 i] at h
    simp only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.reduceAdd] at h
    exact h
  · have h := preserved 64 (by decide)
    have h' : u.external[frameBase s+328]? = t.external[frameBase s+328]? := by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
    exact h'.trans state.tag
  · exact (g.read (n := 8) (r := 5) (by simp [constantSetupEffect,Effect.components])).trans state.choice
  · have h : b.regValue .rax = stackPtr t+1032 := eB.writes.2.1
    exact (gU.read (n := 64) (r := 0) (by simp)).trans (h.trans (congrArg (fun p => p+1032) spT))
  · exact (g.read (n := 64) (r := 2) (by simp [constantSetupEffect,Effect.components])).trans state.rdx

end P256.Proofs.PublicPoint.Normalize.Finish
