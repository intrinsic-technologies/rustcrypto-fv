import P256.Proofs.Verifying.Core.Finish.CopyCoordinates
import P256.Proofs.Verifying.Core.Finish.SetupResult
import P256.Proofs.Verifying.Core.Finish.Movsq

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

structure Saved [Bindings] (s t : RamState) (x y r : Nat) (nonzero : Bool) : Prop extends FrameState s t 24 9992 1176 where
  rip : t.RIP = 0x10dfa2
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  x : MontgomeryAt t (frameBase s + 128)
    x
  y : MontgomeryAt t (frameBase s + 160)
    y
  tag : t.external[frameBase s + 192]? = some 0
  choice : (t.regValue .rbx).setWidth 8 = if nonzero then 1 else 0
  scalar : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s + 704) r
  rdx : t.regValue .rdx = frameBase s + 128

set_option maxRecDepth 2048 in
theorem save_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y r : Nat} {nonzero : Bool} (pre : CalleePre s boundary 0x10d570 72 24 9992)
    (state : Coordinates s t x y r nonzero) : ∃ n u, Advances boundary n t u ∧ Saved s u x y r nonzero := by
  obtain ⟨n,a,runA,frameA,ripA,xA,yA,tagA,gA⟩ := copy_coordinates pre state
  obtain ⟨m,b,runB,frameB,eB⟩ := copy_setup_correct pre frameA ripA
  have memB : b.external = a.external := eB.agrees.external
    (by simp [copySetupEffect,Effect.components,Component.Covers])
  have spA : stackPtr a = frameBase s := frameA.rsp
  have spB : stackPtr b = frameBase s := frameB.rsp
  have src : b.regValue .rsi = frameBase s + 576 := by
    have h : b.regValue .rsi = a.regValue .r15 := eB.writes.2.2.2
    have ha : a.regValue .r15 = t.regValue .r15 := gA.read (n := 64) (r := 15) (by simp)
    rw [h, ha, state.r15]
  have dst : b.regValue .rdi = frameBase s + 128 := by
    have h : b.regValue .rdi = stackPtr a + 128 := eB.writes.2.2.1
    exact h.trans (congrArg (fun p => p+128) spA)
  have srcN : (b.regValue .rsi).toNat = (stackPtr s).toNat-600 := by
    rw [src]
    have addr : frameBase s+576 = stackPtr s-600 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  have dstN : (b.regValue .rdi).toNat = (stackPtr s).toNat-1048 := by
    rw [dst]
    have addr : frameBase s+128 = stackPtr s-1048 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  obtain ⟨u,runU,frameU,ripU,bytes,gU⟩ := movsq72 pre frameB 0xdf9f 128
    (by decide) (by decide) (by decide +kernel) eB.rip
    (by rw [dst,spB]; rfl) eB.writes.2.1
    (by rw [src,← spB]; exact stack_readable (frameOffset := 1176) pre frameB (by decide) (by decide))
    (by rw [srcN,dstN]; have := stack_bounds pre.stack; right; omega)
  rw [src,dst] at bytes
  have g := (gA.trans eB.agrees).trans gU
  refine ⟨n+m+9,u,(runA.trans runB).trans runU,frameU,ripU,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans _ state.output
    apply memLoad_congr (n := 64)
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    apply g.byte
    intro c hc ha
    simp only [copySetupEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)|rfl)|(rfl|rfl|rfl|rfl|rfl)
    all_goals try exact ha.elim
    all_goals try rw [dst] at ha
    all_goals obtain ⟨j,hj,he⟩ := ha
    · exact RangeApart.offsets (frameBase s) (a := 608) (b := 384)
        (by decide) (by decide) (Or.inr (by decide)) j hj i hi he.symm
    · exact RangeApart.offsets (frameBase s) (a := 128) (b := 384)
        (by decide) (by decide) (Or.inl (by decide)) j hj i hi he.symm
  · apply xA.of_bytes_eq
    intro i hi
    rw [bytes i (by omega),memB]
  · apply yA.of_bytes_eq
    intro i hi
    have h := bytes (32+i) (by omega)
    rw [memB] at h
    rw [buffer_add s 128 32 i, buffer_add s 576 32 i] at h
    simp only [BitVec.reduceAdd] at h
    exact h
  · have h := bytes 64 (by decide)
    rw [memB] at h
    have h' : u.external[frameBase s+192]? = a.external[frameBase s+640]? := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h
    exact h'.trans tagA
  · have h := g.read (n := 8) (r := 3) (by simp [copySetupEffect,Effect.components])
    exact h.trans state.choice
  · refine ⟨state.scalar.1, fun i hi => ?_⟩
    rw [← state.scalar.2 i hi]
    apply g.byte
    intro c hc ha
    simp only [copySetupEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)|rfl)|(rfl|rfl|rfl|rfl|rfl)
    all_goals try exact ha.elim
    all_goals try rw [dst] at ha
    all_goals obtain ⟨j,hj,he⟩ := ha
    · exact RangeApart.offsets (frameBase s) (a := 608) (b := 704)
        (by decide) (by decide) (Or.inl (by decide)) j hj i hi he.symm
    · exact RangeApart.offsets (frameBase s) (a := 128) (b := 704)
        (by decide) (by decide) (Or.inl (by decide)) j hj i hi he.symm
  · have h : b.regValue .rdx = stackPtr a+128 := eB.writes.1
    exact (gU.read (n := 64) (r := 2) (by simp)).trans (h.trans (congrArg (fun p => p+128) spA))

end P256.Proofs.Verifying.Core.Finish
