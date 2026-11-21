import P256.Proofs.EcdhWrapper.Scalar.Prefix.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.EcdhWrapper.Copy (copyComponents)

theorem Entry.prefix_facts [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (entry : Entry initial s secret) (result : CalleeResult s t (returnBoundary initial) 33 72) :
    MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
    t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control ∧
    (∀ cap : Bool, memLoad t.external (stackPtr initial-(if cap then 464 else 472)) 64 =
      initial.regValue (if cap then .r8 else .rcx)) := by
  obtain ⟨a,u,v,guarded,setup,copied,agrees⟩ := entry.history
  have setupAgrees : AgreesExcept [.reg 13,.mem (stackPtr a+32) 8,
      .mem (stackPtr a+40) 8,.rip] a u := by
    simpa [Copy.setupEffect,Effect.components,Write.component,Operand.component] using setup.agrees
  have rspU : stackPtr u = stackPtr initial-504 :=
    (setupAgrees.read (n := 64) (r := 4) (by simp)).trans guarded.rsp
  have addr32 : stackPtr a+32 = stackPtr initial-472 := by
    rw [guarded.rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have addr40 : stackPtr a+40 = stackPtr initial-464 := by
    rw [guarded.rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have addrCopy : stackPtr u+112 = stackPtr initial-392 := by
    rw [rspU]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have g := (setupAgrees.trans copied.agrees).trans agrees
  have localFrame : MemoryWriteFrame a s (wrapperRegions ecdhDiffieHellman initial) := by
    apply g.memoryWriteFrame
    intro c hc x hx
    simp only [copyComponents,callComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact hx.elim
    all_goals refine ⟨callStack ecdhDiffieHellman initial,by simp [wrapperRegions],?_⟩
    · rw [addr32] at hx
      exact stack_component_within call.stackAvailable.1 (offset := 472) (by decide) (by decide) hx
    · rw [addr40] at hx
      exact stack_component_within call.stackAvailable.1 (offset := 464) (by decide) (by decide) hx
    · rw [addrCopy] at hx
      exact stack_component_within call.stackAvailable.1 (offset := 392) (by decide) (by decide) hx
    · exact stack_component_within call.stackAvailable.1 (offset := 512) (by decide) (by decide) hx
  have frame := result.stack_frame call.stackAvailable.1 entry.rsp entry.output
    (savedBytes := 48) (by decide) (by decide) (by decide) (by decide)
  have entire := guarded.agrees.trans g
  refine ⟨memoryWriteFrame_trans (memoryWriteFrame_trans guarded.frame localFrame)
    (prefix_work_frame call.stackAvailable.1 frame),
    result.mxcsr.trans (entire.mxcsr (by simp [saveFrame,arenaComponents,guardComponents,copyComponents,callComponents])),
    result.fp87.trans (entire.fcw (by simp [saveFrame,arenaComponents,guardComponents,copyComponents,callComponents])),?_⟩
  intro cap
  have value : memLoad u.external (stackPtr initial-(if cap then 464 else 472)) 64 =
      initial.regValue (if cap then .r8 else .rcx) := by
    cases cap
    · have h : memLoad u.external (stackPtr a+32) 64 = a.regValue .rcx := setup.writes.2.1
      rw [addr32,guarded.output] at h
      exact h
    · have h : memLoad u.external (stackPtr a+40) 64 = a.regValue .r8 := setup.writes.2.2
      rw [addr40,guarded.capacity] at h
      exact h
  have off : stackPtr initial-(if cap then 464 else 472) =
      stackPtr initial-BitVec.ofNat 64 (if cap then 464 else 472) := by cases cap <;> rfl
  rw [off]
  rw [entry.result_word call result (by cases cap <;> decide) (.inr (by cases cap <;> decide))]
  rw [memLoad_agrees_apart agrees (by
    intro addr len member
    have eq : addr = stackPtr initial-512 ∧ len = 8 := by simpa [callComponents] using member
    obtain ⟨rfl,rfl⟩ := eq
    exact stack_sub_apart call.stackAvailable.1 (a := 512) (b := if cap then 464 else 472)
      (by decide) (by cases cap <;> decide) (by decide) (by cases cap <;> decide)
      (.inl (by cases cap <;> decide)))]
  rw [memLoad_agrees_apart copied.agrees (by
    intro addr len member
    have eq : addr = stackPtr u+112 ∧ len = 32 := by simpa [copyComponents] using member
    obtain ⟨rfl,rfl⟩ := eq
    rw [addrCopy]
    exact stack_sub_apart call.stackAvailable.1 (a := 392) (b := if cap then 464 else 472)
      (by decide) (by cases cap <;> decide) (by decide) (by cases cap <;> decide)
      (.inr (by cases cap <;> decide)))]
  simpa only [off] using value

end P256.Proofs.EcdhWrapper.Scalar
