import P256.Proofs.EcdhWrapper.Nonzero.ClearBlock
import P256.Proofs.EcdhWrapper.Nonzero.Memory
import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem clear_pre [Bindings] {initial t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP = 0x1068d7) (rsp : stackPtr t = stackPtr initial - 504) : ClearPre t := by
  refine ⟨rip,?_,?_⟩
  · intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [rsp]
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 312) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 320) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 328) (len := 8) (by decide) (by decide) (by decide)
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
          (offset := 336) (len := 8) (by decide) (by decide) (by decide)
  · intro off member codeOffset codeLength bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [rsp]
    all_goals simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 312) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 320) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 328) (len := 8) (by decide) (by decide) bound
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using
        stack_buffer_code_apart call.stackAvailable.1 (call_stack_avoids call)
          (offset := 336) (len := 8) (by decide) (by decide) bound


theorem clear [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x1068d7) (rsp : stackPtr s = stackPtr initial-504) :
    ∃ n u, Advances (returnBoundary initial) n s u ∧ ReadyToStep u ∧ u.RIP = 0x106907 ∧
      stackPtr u = stackPtr initial-504 ∧
      SecretKeyFromBytes.Scalar.Nat256At u (stackPtr initial-336) 0 ∧
      AgreesExcept (clobbers initial) s u := by
  obtain ⟨n,u,run,readyU,_,effect⟩ := clear_words (returnBoundary initial) outside s ready
    (clear_loaded loaded) (clear_pre call grow rip rsp)
  have ag : AgreesExcept (clobbers initial) s u := by
    have g := effect.agrees
    simp only [clearEffect,Effect.components,List.map_cons,List.map_nil,Write.component_mem,
      List.cons_append,List.nil_append] at g
    rw [rsp] at g
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] at g
    apply g.mono
    simp [clobbers,BitVec.sub_eq_add_neg]
  have stackU : stackPtr u = stackPtr initial-504 :=
    (effect.agrees.read (n := 64) (r := 4) (by simp [clearEffect,Effect.components])).trans rsp
  refine ⟨n,u,run,readyU,effect.rip,stackU,?_,ag⟩
  apply Field.Inverse.nat256At_zero_limbs
  · exact (readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 336) (len := 32) (by decide) (by decide))
      (fun a ha => ag.grow a (grow a ha))).mem
  · have words := effect.writes
    change memLoad u.external (stackPtr s+192) 64 = 0 ∧
      memLoad u.external (stackPtr s+184) 64 = 0 ∧
      memLoad u.external (stackPtr s+176) 64 = 0 ∧
      memLoad u.external (stackPtr s+168) 64 = 0 at words
    rw [rsp] at words
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.reduceNeg,BitVec.reduceAdd,BitVec.add_zero] using
      And.intro words.2.2.2 (And.intro words.2.2.1 (And.intro words.2.1 words.1))

end P256.Proofs.EcdhWrapper.Nonzero
