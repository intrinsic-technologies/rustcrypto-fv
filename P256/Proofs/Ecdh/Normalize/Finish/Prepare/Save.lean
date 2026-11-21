import P256.Proofs.Ecdh.Normalize.Finish.Prepare.CopyCoordinates
import P256.Proofs.Ecdh.Normalize.Finish.Prepare.SetupResult
import P256.Proofs.Ecdh.Normalize.Finish.Prepare.Movsq

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

structure Saved [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x100499
  output : t.regValue .rbx = s.regValue .rdi
  x : MontgomeryAt t (frameBase s + 1016)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : MontgomeryAt t (frameBase s + 1048)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  tag : t.external[frameBase s + 1080]? = some 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  rdx : t.regValue .rdx = frameBase s + 1016

set_option maxRecDepth 2048 in
theorem save_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Coordinates s t boundary point) : ∃ u, Saved s u boundary point := by
  obtain ⟨n,a,runA,frameA,ripA,xA,yA,tagA,gA⟩ := copy_coordinates pre state
  obtain ⟨m,b,runB,frameB,eB⟩ := copy_setup_correct pre frameA ripA
  have memB : b.external = a.external := eB.agrees.external
    (by simp [copySetupEffect,Effect.components,Component.Covers])
  have spA : stackPtr a = frameBase s := frameA.rsp
  have spB : stackPtr b = frameBase s := frameB.rsp
  have src : b.regValue .rsi = frameBase s + 248 := by
    have h : b.regValue .rsi = a.regValue .r15 := eB.writes.2.2.2
    have ha : a.regValue .r15 = t.regValue .r15 := gA.read (n := 64) (r := 15) (by simp)
    rw [h, ha, state.r15]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have dst : b.regValue .rdi = frameBase s + 1016 := by
    have h : b.regValue .rdi = stackPtr a + 1016 := eB.writes.2.2.1
    exact h.trans (congrArg (fun p => p+1016) spA)
  have srcN : (b.regValue .rsi).toNat = (stackPtr s).toNat-1808 := by
    rw [src]
    have addr : frameBase s+248 = stackPtr s-1808 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  have dstN : (b.regValue .rdi).toNat = (stackPtr s).toNat-1040 := by
    rw [dst]
    have addr : frameBase s+1016 = stackPtr s-1040 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  obtain ⟨u,runU,frameU,ripU,bytes,gU⟩ := movsq72 pre frameB 0x496 1016
    (by decide) (by decide) (by decide +kernel) eB.rip
    (by rw [dst,spB]; rfl) eB.writes.2.1
    (by rw [src,← spB]; exact stack_readable (frameOffset := 2056) pre frameB (by decide) (by decide))
    (by rw [srcN,dstN]; have := stack_bounds pre.stack; left; omega)
  rw [src,dst] at bytes
  have g := (gA.trans eB.agrees).trans gU
  refine ⟨u,frameU,?_,ripU,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨fuel,run⟩ := state.execution
    exact ⟨fuel+n+m+9,((run.trans runA).trans runB).trans runU⟩
  · exact (g.read (n := 64) (r := 3) (by simp [copySetupEffect,Effect.components])).trans state.output
  · apply xA.of_bytes_eq
    intro i hi
    rw [bytes i (by omega),memB]
  · apply yA.of_bytes_eq
    intro i hi
    have h := bytes (32+i) (by omega)
    rw [memB] at h
    rw [buffer_add s 1016 32 i, buffer_add s 248 32 i] at h
    simp only [BitVec.reduceAdd] at h
    exact h
  · have h := bytes 64 (by decide)
    rw [memB] at h
    have h' : u.external[frameBase s+1080]? = a.external[frameBase s+312]? := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h
    exact h'.trans tagA
  · have h := g.read (n := 8) (r := 5) (by simp [copySetupEffect,Effect.components])
    exact h.trans state.choice
  · have h : b.regValue .rdx = stackPtr a+1016 := eB.writes.1
    exact (gU.read (n := 64) (r := 2) (by simp)).trans (h.trans (congrArg (fun p => p+1016) spA))

end P256.Proofs.Ecdh.Normalize.Finish
