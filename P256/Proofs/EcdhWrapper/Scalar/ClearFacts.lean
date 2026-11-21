import P256.Proofs.EcdhWrapper.Scalar.ClearRun
import P256.Proofs.EcdhWrapper.Scalar.Preserve

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem clear_preserved [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (rsp : stackPtr s = stackPtr initial-504) (effect : (clearEffect s).Holds s t)
    {offset len : Nat} (bound : offset ≤ 128) (extent : len ≤ offset+8)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc cover
  simp only [clearEffect,Effect.components,List.map_cons,List.map_nil,
    Write.component_mem,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨j,hj,eq⟩ := cover
  all_goals rw [rsp] at eq
  · apply stack_sub_apart call.stackAvailable.1 (a := 432) (b := offset)
      (by decide) (by change offset ≤ 4104; omega) (by decide) extent (.inl (by omega)) j hj i hi
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
      using eq.symm
  · apply stack_sub_apart call.stackAvailable.1 (a := 440) (b := offset)
      (by decide) (by change offset ≤ 4104; omega) (by decide) extent (.inl (by omega)) j hj i hi
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
      using eq.symm
  · apply stack_sub_apart call.stackAvailable.1 (a := 448) (b := offset)
      (by decide) (by change offset ≤ 4104; omega) (by decide) extent (.inl (by omega)) j hj i hi
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
      using eq.symm
  · apply stack_sub_apart call.stackAvailable.1 (a := 456) (b := offset)
      (by decide) (by change offset ≤ 4104; omega) (by decide) extent (.inl (by omega)) j hj i hi
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
      using eq.symm

theorem clear_loaded_after [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (rsp : stackPtr s = stackPtr initial-504) (effect : (clearEffect s).Holds s t)
    (loaded : ProgramLoaded s) : ProgramLoaded t := by
  intro a b hf
  rw [effect.agrees.byte]
  · exact loaded a b hf
  · intro c hc cover
    simp only [clearEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_mem,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨i,hi,eq⟩ := cover
    all_goals rw [rsp] at eq
    · have contains := stack_component_within call.stackAvailable.1 (offset := 432)
        (len := 8) (by decide) (by decide) (address := a) ⟨i,hi,by
          simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
            using eq⟩
      exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 a contains
        (.inl ⟨b,hf⟩)
    · have contains := stack_component_within call.stackAvailable.1 (offset := 440)
        (len := 8) (by decide) (by decide) (address := a) ⟨i,hi,by
          simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
            using eq⟩
      exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 a contains
        (.inl ⟨b,hf⟩)
    · have contains := stack_component_within call.stackAvailable.1 (offset := 448)
        (len := 8) (by decide) (by decide) (address := a) ⟨i,hi,by
          simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
            using eq⟩
      exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 a contains
        (.inl ⟨b,hf⟩)
    · have contains := stack_component_within call.stackAvailable.1 (offset := 456)
        (len := 8) (by decide) (by decide) (address := a) ⟨i,hi,by
          simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
            using eq⟩
      exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 a contains
        (.inl ⟨b,hf⟩)

end P256.Proofs.EcdhWrapper.Scalar
