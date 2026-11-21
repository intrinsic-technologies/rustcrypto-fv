import P256.Proofs.PublicPoint.Normalize.Finish.Selected
import P256.Proofs.PublicPoint.Normalize.Finish.SelectSetup
import P256.Proofs.PublicPoint.Normalize.OutputSelect

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

def firstSite : OutputSelect.Site :=
  ⟨0xeac1,0x58ba,by decide,by decide +kernel,by decide,
    912,by decide,by decide,1680,by decide,by decide,0,by decide⟩

def secondSite : OutputSelect.Site :=
  ⟨0xeadc,0x589f,by decide,by decide +kernel,by decide,
    880,by decide,by decide,1648,by decide,by decide,32,by decide⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem select [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Prepared s t boundary point) : ∃ u, Selected s u boundary point := by
  obtain ⟨n,a,runA,readyA,_,eA⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xeab9 selectFirstBytes
      (by decide) (by decide +kernel)) state.rip
  have frameA := state.toFrameState.after_registers readyA eA.agrees
    (by simp [selectFirstEffect,Effect.components,Component.Covers])
    (by simp [selectFirstEffect,Effect.components])
  have memA : a.external = t.external := eA.agrees.external
    (by simp [selectFirstEffect,Effect.components,Component.Covers])
  have inputA : a.regValue .rsi = stackPtr s-912 := by
    have h : a.regValue .rsi = t.regValue .rax := eA.writes.2.1
    rw [h,state.rax]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have rightA : a.regValue .rdx = stackPtr s-1680 := by
    have h : a.regValue .rdx = t.regValue .rdx :=
      eA.agrees.read (n := 64) (r := 2) (by simp [selectFirstEffect,Effect.components])
    rw [h,state.rdx]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have outputA : a.regValue .rdi = s.regValue .rdi := eA.writes.1.trans state.output
  have xA : MontgomeryAt a (stackPtr s-1680)
      (point.x * Curve.inverse domain.p point.z % domain.p) := by
    have h := state.x.of_bytes_eq (t := a) (fun _ _ => congrArg (fun m => m[_]?) memA)
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  have zeroA : MontgomeryAt a (stackPtr s-912) 0 := by
    have h := state.zeroX.of_bytes_eq (t := a) (fun _ _ => congrArg (fun m => m[_]?) memA)
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  have choiceA : (a.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    have h := select_flag state.choice eA.writes.2.2
    by_cases hz : point.z=0 <;> simpa [hz] using h
  obtain ⟨m,b,runB,frameB,ripB,xB,savedB,stackB,_⟩ := OutputSelect.select_call pre frameA firstSite
    eA.rip inputA rightA (by simpa only [firstSite,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using outputA)
    zeroA xA choiceA
  obtain ⟨k,c,runC,readyC,_,eC⟩ := select_second_setup boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameB.loaded) 0xeac6 selectSecondBytes
      (by decide) (by decide +kernel)) ripB
  have frameC := frameB.after_registers readyC eC.agrees
    (by simp [selectSecondEffect,Effect.components,Component.Covers])
    (by simp [selectSecondEffect,Effect.components])
  have memC : c.external = b.external := eC.agrees.external
    (by simp [selectSecondEffect,Effect.components,Component.Covers])
  have outB : b.regValue .rbx = s.regValue .rdi :=
    (savedB .rbx (by simp)).trans
      ((eA.agrees.read (n := 64) (r := 3) (by simp [selectFirstEffect,Effect.components])).trans state.output)
  have choiceB : (b.regValue .rbp).setWidth 8 = if point.z=0 then 0 else 1 :=
    (congrArg (BitVec.setWidth 8) (savedB .rbp (by simp))).trans
      ((eA.agrees.read (n := 8) (r := 5) (by simp [selectFirstEffect,Effect.components])).trans state.choice)
  have inputC : c.regValue .rsi = stackPtr s-880 := by
    have h : c.regValue .rsi = stackPtr b+1064 := eC.writes.1
    rw [h,frameB.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have rightC : c.regValue .rdx = stackPtr s-1648 := by
    have h : c.regValue .rdx = stackPtr b+296 := eC.writes.2.1
    rw [h,frameB.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have outputC : c.regValue .rdi = s.regValue .rdi+32 := by
    have h : c.regValue .rdi = b.regValue .rbx+32 := eC.writes.2.2.1
    rw [h,outB]
  have yT : MontgomeryAt t (stackPtr s-1648)
      (point.y * Curve.inverse domain.p point.z % domain.p) := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.y
  have zeroT : MontgomeryAt t (stackPtr s-880) 0 := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.zeroY
  have yC := yT.of_bytes_eq (t := c) (fun i hi => by
    rw [memC,stackB 1648 32 (by decide) (by decide) i hi,memA]
    rfl)
  have zeroC := zeroT.of_bytes_eq (t := c) (fun i hi => by
    rw [memC,stackB 880 32 (by decide) (by decide) i hi,memA]
    rfl)
  have choiceC : (c.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    have h := select_flag choiceB eC.writes.2.2.2
    by_cases hz : point.z=0 <;> simpa [hz] using h
  obtain ⟨l,u,runU,frameU,ripU,yU,savedU,stackU,outputU⟩ := OutputSelect.select_call pre frameC secondSite
    eC.rip inputC rightC outputC zeroC yC choiceC
  have xU : MontgomeryAt u (s.regValue .rdi)
      (if point.z=0 then 0 else point.x * Curve.inverse domain.p point.z % domain.p) := by
    have h : MontgomeryAt b (s.regValue .rdi)
        (if point.z=0 then 0 else point.x * Curve.inverse domain.p point.z % domain.p) := by
      by_cases hz : point.z=0 <;> simpa [hz,firstSite] using xB
    apply h.of_bytes_eq
    intro i hi
    rw [outputU i (by omega) (.inl hi),memC]
  have yU' : MontgomeryAt u (s.regValue .rdi+32)
      (if point.z=0 then 0 else point.y * Curve.inverse domain.p point.z % domain.p) := by
    by_cases hz : point.z=0 <;> simpa [hz,secondSite] using yU
  refine ⟨u,frameU,?_,ripU,?_,xU,yU',?_,?_⟩
  · obtain ⟨fuel,run⟩ := state.execution
    exact ⟨fuel+n+m+k+l,(((run.trans runA).trans runB).trans runC).trans runU⟩
  · exact (savedU .rbx (by simp)).trans
      ((eC.agrees.read (n := 64) (r := 3) (by simp [selectSecondEffect,Effect.components])).trans outB)
  · have tagT : t.external[stackPtr s-1616]? = some 0 := by
      simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.tag
    have h := stackU 1616 1 (by decide) (by decide) 0 (by decide)
    simp only [BitVec.add_zero] at h
    rw [memC] at h
    have hB := stackB 1616 1 (by decide) (by decide) 0 (by decide)
    simp only [BitVec.add_zero] at hB
    rw [hB,memA] at h
    have ht : u.external[stackPtr s-1616]? = some 0 := h.trans tagT
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using ht
  · exact (congrArg (BitVec.setWidth 8) (savedU .rbp (by simp))).trans
      ((eC.agrees.read (n := 8) (r := 5) (by simp [selectSecondEffect,Effect.components])).trans choiceB)

end P256.Proofs.PublicPoint.Normalize.Finish
