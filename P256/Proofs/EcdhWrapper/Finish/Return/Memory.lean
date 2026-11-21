import P256.Proofs.EcdhWrapper.Finish.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {secret peer : ByteArray} {slices : Array Input}

def components (initial : RamState) : List Component :=
  [.mem (stackPtr initial-504) 32,.mem (initial.regValue .rcx) 8,.reg 0,.reg 2,.reg 5,.flags,.rip]

theorem loaded_after (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (loaded : ProgramLoaded s) (ag : AgreesExcept (components initial) s t) : ProgramLoaded t := by
  intro a b hb
  rw [ag.byte ?_]
  · exact loaded a b hb
  · intro c hc cover
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    · exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 a
        (stack_component_within (routine := ecdhDiffieHellman) call.stackAvailable.1
          (offset := 504) (by decide) (by decide) cover) (.inl ⟨b,hb⟩)
    · exact Copy.output_avoids call a (Copy.output_contains call (off := 0) (len := 8)
        (by decide) (by simpa only [BitVec.add_zero] using cover)) (.inl ⟨b,hb⟩)

theorem stack_word (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ag : AgreesExcept (components initial) s t) {off : Nat} (bound : off≤48) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64=
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
  apply memLoad_agrees_apart ag
  intro a len hm
  simp only [components,List.mem_cons,List.not_mem_nil,or_false,Component.mem.injEq,reduceCtorEq] at hm
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact stack_sub_apart call.stackAvailable.1 (a := 504) (b := off)
      (by decide) (by change off≤4104; omega) (by decide) (by omega) (.inl (by omega))
  · simpa only [BitVec.add_zero] using Copy.output_stack call (outOff := 0) (outLen := 8)
      (by omega : off≤4104) (by omega : 8≤off+8) (by decide)

theorem payload (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ag : AgreesExcept (components initial) s t) {bytes : ByteArray}
    (data : (MemoryRegion.mk (initial.regValue .rcx+8).toNat 32).HasBytes s.external bytes) :
    (MemoryRegion.mk (initial.regValue .rcx+8).toNat 32).HasBytes t.external bytes := by
  apply hasBytes_agrees_apart ag _ data
  intro a len hm
  simp only [components,List.mem_cons,List.not_mem_nil,or_false,Component.mem.injEq,reduceCtorEq] at hm
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · intro i hi j hj eq
    exact Copy.output_stack call (off := 504) (len := 32) (outOff := 8) (outLen := 32)
      (by decide) (by decide) (by decide) j hj i hi eq.symm
  · intro i hi j hj eq
    apply (show OffsetsApart 0 8 8 32 by unfold OffsetsApart; decide +kernel).ne
      (initial.regValue .rcx) hi hj (by decide)
    simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using eq

theorem local_frame (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ag : AgreesExcept (components initial) s t) :
    MemoryWriteFrame s t #v[outputRegion ecdhDiffieHellman initial [secret,peer],
      allocatorStateRegion,randomSourceRegion,callStack ecdhDiffieHellman initial] := by
  apply ag.memoryWriteFrame
  intro c hc a cover
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · exact ⟨callStack ecdhDiffieHellman initial,by simp,
      stack_component_within (routine := ecdhDiffieHellman) call.stackAvailable.1
        (offset := 504) (by decide) (by decide) cover⟩
  · refine ⟨outputRegion ecdhDiffieHellman initial [secret,peer],by simp,?_⟩
    rw [Copy.output_eq]
    exact Copy.output_contains call (off := 0) (len := 8) (by decide)
      (by simpa only [BitVec.add_zero] using cover)

end P256.Proofs.EcdhWrapper.Finish.Return
