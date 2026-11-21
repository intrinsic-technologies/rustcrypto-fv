import P256.Proofs.PublicPoint.Normalize.Finish.CopyCoordinates
import P256.Proofs.PublicPoint.Normalize.Finish.SetupResult
import P256.Proofs.PublicPoint.Normalize.Finish.Movsq

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

structure Saved [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10ea97
  output : t.regValue .rbx = s.regValue .rdi
  x : MontgomeryAt t (frameBase s + 264)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : MontgomeryAt t (frameBase s + 296)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  tag : t.external[frameBase s + 328]? = some 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  rdx : t.regValue .rdx = frameBase s + 264

set_option maxRecDepth 2048 in
theorem save_coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Coordinates s t boundary point) : ∃ u, Saved s u boundary point := by
  obtain ⟨n,a,runA,frameA,ripA,xA,yA,tagA,gA⟩ := copy_coordinates pre state
  obtain ⟨m,b,runB,frameB,eB⟩ := copy_setup_correct pre frameA ripA
  have memB : b.external = a.external := eB.agrees.external
    (by simp [copySetupEffect,Effect.components,Component.Covers])
  have spA : stackPtr a = frameBase s := frameA.rsp
  have spB : stackPtr b = frameBase s := frameB.rsp
  have src : b.regValue .rsi = frameBase s + 1032 := by
    have h : b.regValue .rsi = a.regValue .r15 := eB.writes.2.2.2
    have ha : a.regValue .r15 = t.regValue .r15 := gA.read (n := 64) (r := 15) (by simp)
    rw [h, ha, state.r15]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have dst : b.regValue .rdi = frameBase s + 264 := by
    have h : b.regValue .rdi = stackPtr a + 264 := eB.writes.2.2.1
    exact h.trans (congrArg (fun p => p+264) spA)
  have srcN : (b.regValue .rsi).toNat = (stackPtr s).toNat-912 := by
    rw [src]
    have addr : frameBase s+1032 = stackPtr s-912 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  have dstN : (b.regValue .rdi).toNat = (stackPtr s).toNat-1680 := by
    rw [dst]
    have addr : frameBase s+264 = stackPtr s-1680 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact stack_sub_toNat pre.stack (by decide)
  obtain ⟨u,runU,frameU,ripU,bytes,gU⟩ := movsq72 pre frameB 0xea94 264
    (by decide) (by decide) (by decide +kernel) eB.rip
    (by rw [dst,spB]; rfl) eB.writes.2.1
    (by rw [src,← spB]; exact stack_readable (frameOffset := 1944) pre frameB (by decide) (by decide))
    (by rw [srcN,dstN]; have := stack_bounds pre.stack; right; omega)
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
    rw [buffer_add s 264 32 i, buffer_add s 1032 32 i] at h
    simp only [BitVec.reduceAdd] at h
    exact h
  · have h := bytes 64 (by decide)
    rw [memB] at h
    have h' : u.external[frameBase s+328]? = a.external[frameBase s+1096]? := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h
    exact h'.trans tagA
  · have h := g.read (n := 8) (r := 5) (by simp [copySetupEffect,Effect.components])
    exact h.trans state.choice
  · have h : b.regValue .rdx = stackPtr a+264 := eB.writes.1
    exact (gU.read (n := 64) (r := 2) (by simp)).trans (h.trans (congrArg (fun p => p+264) spA))

end P256.Proofs.PublicPoint.Normalize.Finish
