import P256.Proofs.EcdhWrapper.Scalar.Entry
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.EcdhWrapper.Copy (copyComponents)

theorem Entry.result_word [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (entry : Entry initial s secret) (result : CalleeResult s t (returnBoundary initial) 33 72)
    {offset : Nat} (bound : offset ≤ 504)
    (apart : offset + 33 ≤ 128 ∨ 136 ≤ offset) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 = _
  rw [result.stack_byte call.stackAvailable.1 entry.rsp entry.output
    (frameOffset := 504) (len := 8) (by decide) (by decide) bound (by omega) apart hi]
  rfl

theorem Entry.saved_words [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (entry : Entry initial s secret) (result : CalleeResult s t (returnBoundary initial) 33 72) :
    (∀ reg ∈ savedRegisters,
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 reg.2) 64 =
        initial.regValue reg.1) ∧
    memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
  obtain ⟨a,u,v,guarded,setup,copied,agrees⟩ := entry.history
  have setupAgrees :
      AgreesExcept [.reg 13,.mem (stackPtr a+32) 8,.mem (stackPtr a+40) 8,.rip] a u := by
    simpa [Copy.setupEffect,Effect.components,Write.component,Operand.component] using setup.agrees
  have setupRsp : stackPtr u = stackPtr initial - 504 :=
    (setupAgrees.read (n := 64) (r := 4) (by simp)).trans guarded.rsp
  have copiedAddress : stackPtr u+112 = stackPtr initial - 392 := by
    rw [setupRsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have preserved (offset : Nat) (bound : offset ≤ 48) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad a.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    rw [entry.result_word call result (by omega) (.inl (by omega))]
    rw [memLoad_agrees_apart agrees (by
      intro address len member
      have eq : address = stackPtr initial - 512 ∧ len = 8 := by
        simpa [callComponents] using member
      obtain ⟨rfl,rfl⟩ := eq
      exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := offset)
        (by decide) (by change offset ≤ 4104; omega) (by decide) (by omega) (.inl (by omega)))]
    rw [memLoad_agrees_apart copied.agrees (by
      intro address len member
      have eq : address = stackPtr u+112 ∧ len = 32 := by
        simpa [copyComponents] using member
      obtain ⟨rfl,rfl⟩ := eq
      rw [copiedAddress]
      exact stack_sub_apart call.stackAvailable.1 (a := 392) (b := offset)
        (by decide) (by change offset ≤ 4104; omega) (by decide) (by omega) (.inl (by omega)))]
    apply memLoad_agrees_apart setupAgrees
    intro address len member
    have eq : (address = stackPtr a+32 ∧ len = 8) ∨
        (address = stackPtr a+40 ∧ len = 8) := by simpa using member
    rcases eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have addr : stackPtr a+32 = stackPtr initial - 472 := by
        rw [guarded.rsp]
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [addr]
      exact stack_sub_apart call.stackAvailable.1 (a := 472) (b := offset)
        (by decide) (by change offset ≤ 4104; omega) (by decide) (by omega) (.inl (by omega))
    · have addr : stackPtr a+40 = stackPtr initial - 464 := by
        rw [guarded.rsp]
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      rw [addr]
      exact stack_sub_apart call.stackAvailable.1 (a := 464) (b := offset)
        (by decide) (by change offset ≤ 4104; omega) (by decide) (by omega) (.inl (by omega))
  constructor
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (preserved reg.2 bound).trans (guarded.saved reg member)
  · have h := preserved 0 (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans guarded.returnAddress


theorem Entry.result_registers [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (entry : Entry initial s secret) (result : CalleeResult s t (returnBoundary initial) 33 72) :
    t.regValue .rbx = stackPtr initial - 128 ∧
    t.regValue .rbp = 32 ∧ t.regValue .r12 = initial.regValue .rdi ∧
    t.regValue .r13 = 2 ∧ t.regValue .r15 = initial.regValue .rdx := by
  obtain ⟨a,u,v,guarded,setup,copied,agrees⟩ := entry.history
  have setupAgrees :
      AgreesExcept [.reg 13,.mem (stackPtr a+32) 8,.mem (stackPtr a+40) 8,.rip] a u := by
    simpa [Copy.setupEffect,Effect.components,Write.component,Operand.component] using setup.agrees
  have afterSetup := copied.agrees.trans agrees
  have entire := setupAgrees.trans afterSetup
  have size : secret.size = 32 := ((arguments_iff secret peer).mp call.argumentsValid).1
  have rbp : a.regValue .rbp = 32 := guarded.length.trans (by rw [size]; rfl)
  have r13 : u.regValue .r13 = 2 := setup.writes.1.trans guarded.count
  refine ⟨(result.calleeSaved .rbx (by simp)).trans entry.rbx,?_,?_,?_,?_⟩
  · exact (result.calleeSaved .rbp (by simp)).trans
      ((entire.read (n := 64) (r := 5) (by simp [copyComponents,callComponents])).trans rbp)
  · exact (result.calleeSaved .r12 (by simp)).trans
      ((entire.read (n := 64) (r := 12) (by simp [copyComponents,callComponents])).trans guarded.pointers)
  · exact (result.calleeSaved .r13 (by simp)).trans
      ((afterSetup.read (n := 64) (r := 13) (by simp [copyComponents,callComponents])).trans r13)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((entire.read (n := 64) (r := 15) (by simp [copyComponents,callComponents])).trans guarded.lengths)

end P256.Proofs.EcdhWrapper.Scalar
