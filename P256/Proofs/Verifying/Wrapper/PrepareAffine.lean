import P256.Proofs.Verifying.Wrapper.KeyTag
import P256.Proofs.Verifying.Wrapper.AffineArguments
import P256.Proofs.Verifying.Wrapper.AffineCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem prepare_affine [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x1030f8) (tag : memLoad s.external (stackPtr initial-208) 64 = 0)
    (represented : Sec1.AffineAt s (stackPtr initial-200) point) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x103118 ∧ Sec1.AffineAt t (stackPtr initial-112) point ∧
      AgreesExcept [.flags,.reg 6,.reg 7,.reg 1,.mem (stackPtr initial-112) 72,.rip] s t ∧
      MemoryWriteFrame s t #v[workRegion initial] := by
  obtain ⟨a,runA,stateA,ripA,memoryA,agA⟩ :=
    key_tag_branch state call.stackAvailable.1 outside rip tag
  have pointA : Sec1.AffineAt a (stackPtr initial-200) point := by
    exact represented.of_bytes_eq (by intro i hi; rw [memoryA])
  obtain ⟨nb,b,runB,readyB,_,effectB⟩ := affine_arguments (returnBoundary initial) outside a
    (readyToStep stateA.machine stateA.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateA.loaded) 0x3103 affineArgumentBytes
      (by decide) (by decide +kernel)) ripA
  have agB : AgreesExcept [.reg 6,.reg 7,.reg 1,.rip] a b := by
    simpa only [affineArgumentEffect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append] using effectB.agrees
  have stateB := stateA.after_registers readyB agB
    (by simp [Component.Covers]) (by simp) (by simp)
  have values : b.regValue .rsi = stackPtr a+80 ∧ b.regValue .rdi = stackPtr a+168 ∧
      b.regValue .rcx = 9 := effectB.writes
  have source : b.regValue .rsi = stackPtr initial-200 := by
    rw [values.1,stateA.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have destination : b.regValue .rdi = stackPtr initial-112 := by
    rw [values.2.1,stateA.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have pointB : Sec1.AffineAt b (stackPtr initial-200) point :=
    pointA.of_bytes_eq (by intro i hi; rw [agB.external (by simp [Component.Covers])])
  obtain ⟨t,runT,stateT,ripT,pointT,agT,frameT⟩ := affine_copy call stateB outside
    effectB.rip source destination values.2.2 pointB
  refine ⟨_,t,(runA.trans runB).trans runT,stateT,ripT,pointT,?_,?_⟩
  · apply ((agA.trans agB).trans agT).mono
    intro c hc
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with ((rfl | rfl) | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro address away
    rw [frameT address away,agB.external (by simp [Component.Covers]),memoryA]

end P256.Proofs.Verifying.Wrapper
