import P256.Proofs.Verifying.Core.Finish.Prepared
import P256.Proofs.Verifying.Core.Finish.SelectSetup
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

def firstSite : FieldCall.BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xdfd0,0x63ab,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,600,280,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩,
    rfl,by decide,1048,by decide,by decide,Or.inl (by decide)⟩

def secondSite : FieldCall.BinaryCallSite 9992 1176 0x114380 128 :=
  ⟨0xdfef,0x638c,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x14380 (by decide),
    ⟨1184,568,248,by decide,by decide,by decide,by decide,by decide,by decide,Or.inl (by decide)⟩,
    rfl,by decide,1016,by decide,by decide,Or.inl (by decide)⟩

structure Selected [Bindings] (s t : RamState) (x r : Nat) (nonzero : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10dff4
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  x : MontgomeryAt t (stackPtr s-280) (if nonzero then x else 0)
  scalar : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s+704) r

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem select [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y r : Nat} {nonzero : Bool} (pre : CalleePre s boundary 0x10d570 72 24 9992)
    (state : Prepared s t x y r nonzero) : ∃ fuel u, Advances boundary fuel t u ∧ Selected s u x r nonzero := by
  obtain ⟨n,a,runA,readyA,_,eA⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdfc3 selectFirstBytes
      (by decide) (by decide +kernel)) state.rip
  have frameA := state.toFrameState.after_registers readyA eA.agrees
    (by simp [selectFirstEffect,Effect.components,Component.Covers])
    (by simp [selectFirstEffect,Effect.components])
  have memA : a.external = t.external := eA.agrees.external
    (by simp [selectFirstEffect,Effect.components,Component.Covers])
  have inputA : a.regValue .rsi = stackPtr s-600 := by
    have h : a.regValue .rsi = t.regValue .rax := eA.writes.2.1
    rw [h,state.rax]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have rightA : a.regValue .rdx = stackPtr s-1048 := by
    have h : a.regValue .rdx = t.regValue .rdx :=
      eA.agrees.read (n := 64) (r := 2) (by simp [selectFirstEffect,Effect.components])
    rw [h,state.rdx]
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have outputA : a.regValue .rdi = stackPtr s-280 := by
    have h : a.regValue .rdi = stackPtr t+896 := eA.writes.1
    rw [h,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have xA : MontgomeryAt a (stackPtr s-1048)
      x := by
    have h := state.x.of_bytes_eq (t := a) (fun _ _ => congrArg (fun m => m[_]?) memA)
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  have zeroA : MontgomeryAt a (stackPtr s-600) 0 := by
    have h := state.zeroX.of_bytes_eq (t := a) (fun _ _ => congrArg (fun m => m[_]?) memA)
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  have choiceA : (a.regValue .rcx).setWidth 8 = if nonzero then 1 else 0 := by
    have h := select_flag state.choice eA.writes.2.2
    exact h
  obtain ⟨m,b,runB,frameB,ripB,xB,savedB,stackB,_⟩ := PublicPoint.Normalize.select_binary_call (op := fun a b => if nonzero then b else a)
    pre frameA firstSite
    (fun v cp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct
      cp hx hy (by rw [hc,choiceA]))
    eA.rip inputA rightA outputA zeroA xA
  obtain ⟨k,c,runC,readyC,_,eC⟩ := select_second_setup boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameB.loaded) 0xdfd5 selectSecondBytes
      (by decide) (by decide +kernel)) ripB
  have frameC := frameB.after_registers readyC eC.agrees
    (by simp [selectSecondEffect,Effect.components,Component.Covers])
    (by simp [selectSecondEffect,Effect.components])
  have memC : c.external = b.external := eC.agrees.external
    (by simp [selectSecondEffect,Effect.components,Component.Covers])
  have choiceB : (b.regValue .rbx).setWidth 8 = if nonzero then 1 else 0 :=
    (congrArg (BitVec.setWidth 8) (savedB .rbx (by simp))).trans
      ((eA.agrees.read (n := 8) (r := 3) (by simp [selectFirstEffect,Effect.components])).trans state.choice)
  have inputC : c.regValue .rsi = stackPtr s-568 := by
    have h : c.regValue .rsi = stackPtr b+608 := eC.writes.1
    rw [h,frameB.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have rightC : c.regValue .rdx = stackPtr s-1016 := by
    have h : c.regValue .rdx = stackPtr b+160 := eC.writes.2.1
    rw [h,frameB.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have outputC : c.regValue .rdi = stackPtr s-248 := by
    have h : c.regValue .rdi = stackPtr b+928 := eC.writes.2.2.1
    rw [h,frameB.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have yT : MontgomeryAt t (stackPtr s-1016)
      y := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.y
  have zeroT : MontgomeryAt t (stackPtr s-568) 0 := by
    simpa only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using state.zeroY
  have yC := yT.of_bytes_eq (t := c) (fun i hi => by
    rw [memC,stackB 1016 32 (by decide) (by decide) (Or.inr (by decide)) i hi,memA]
    rfl)
  have zeroC := zeroT.of_bytes_eq (t := c) (fun i hi => by
    rw [memC,stackB 568 32 (by decide) (by decide) (Or.inr (by decide)) i hi,memA]
    rfl)
  have choiceC : (c.regValue .rcx).setWidth 8 = if nonzero then 1 else 0 := by
    have h := select_flag choiceB eC.writes.2.2.2
    exact h
  obtain ⟨l,u,runU,frameU,ripU,yU,savedU,stackU,outputU⟩ := PublicPoint.Normalize.select_binary_call (op := fun a b => if nonzero then b else a)
    pre frameC secondSite
    (fun v cp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct
      cp hx hy (by rw [hc,choiceC]))
    eC.rip inputC rightC outputC zeroC yC
  have xU : MontgomeryAt u (stackPtr s-280) (if nonzero then x else 0) := by
    apply xB.of_bytes_eq
    intro i hi
    change u.external[stackPtr s-280#64+BitVec.ofNat 64 i]? = b.external[stackPtr s-280#64+BitVec.ofNat 64 i]?
    rw [stackU 280 32 (by decide) (by decide) (Or.inr (by decide)) i hi,memC]
  refine ⟨n+m+k+l,u,((runA.trans runB).trans runC).trans runU,
    frameU,ripU,?_,xU,?_⟩
  · apply Eq.trans _ state.output
    have addr : frameBase s+384 = stackPtr s-792#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    apply memLoad_congr (n := 64)
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [stackU 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi,
      memC,stackB 792 8 (by decide) (by decide) (Or.inr (by decide)) i hi,memA]
  · have addr : frameBase s+704 = stackPtr s-472#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    refine ⟨state.scalar.1,fun i hi => ?_⟩
    rw [addr]
    change u.external[stackPtr s-472#64+BitVec.ofNat 64 i]? = _
    rw [stackU 472 32 (by decide) (by decide) (Or.inr (by decide)) i hi,
      memC,stackB 472 32 (by decide) (by decide) (Or.inr (by decide)) i hi,memA,← addr]
    exact state.scalar.2 i hi

end P256.Proofs.Verifying.Core.Finish
