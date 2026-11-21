import P256.Proofs.EcdhWrapper.Scalar.Clear
import P256.Proofs.EcdhWrapper.Scalar.Entry
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem clear_pre [Bindings] {initial t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = 0x106892) (rsp : stackPtr t = stackPtr initial - 504) : ClearPre t := by
  refine ⟨rip,?_,?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [rsp]
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 432) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 440) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 448) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 456) (len := 8) (by decide) (by decide) (by decide)
  · intro off member codeOffset codeLength bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [rsp]
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 432) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 440) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 448) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 456) (len := 8) (by decide) (by decide) bound

theorem Entry.allocated [Bindings] {initial s : RamState} {secret : ByteArray}
    (entry : Entry initial s secret) :
    ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome := by
  obtain ⟨a,u,v,guarded,setup,copied,agrees⟩ := entry.history
  exact ((guarded.agrees.trans setup.agrees).trans (copied.agrees.trans agrees)).grow

theorem clear_after_decode [bindings : Bindings] {initial s t : RamState}
    {secret peer : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (entry : Entry initial s secret)
    (result : CalleeResult s t (returnBoundary initial) 33 72) :
    ∃ fuel u, Advances (returnBoundary initial) fuel t u ∧ ReadyToStep u ∧
      (clearEffect t).Holds t u := by
  have rsp : stackPtr t = stackPtr initial - 504 := by
    have h : stackPtr t = stackPtr s + 8 := result.rsp
    rw [h,entry.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have pre := clear_pre call
    (fun a ha => result.allocated a (entry.allocated a ha)) (result.rip.trans entry.ret) rsp
  obtain ⟨fuel,u,run,ready,_,effect⟩ := clear_words (returnBoundary initial)
    entry.pre.outerBoundary t (readyToStep result.machine result.bindingsSupported)
    (clear_loaded result.loaded) pre
  exact ⟨fuel,u,run,ready,effect⟩

end P256.Proofs.EcdhWrapper.Scalar
