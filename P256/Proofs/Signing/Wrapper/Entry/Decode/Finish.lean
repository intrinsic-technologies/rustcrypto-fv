import P256.Proofs.Signing.Wrapper.Entry.Decode.ZeroCheck
import P256.Proofs.Signing.Wrapper.Entry.Decode.Output

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem finish [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : CopyEntry initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Decoded initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨n,t,ht,rt,_,et⟩ := output_correct (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x25eb outputBytes
      (by decide) (by decide +kernel))
    (block_pre call state.toState state.rip (by simp) (by simp))
  have st := after_stack call state.toState ht rt et.agrees
    (by
      intro p len hp
      simp only [outputEffect,Effect.components,Write.component,Operand.component,List.map_cons,
        List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
      rcases hp with (h | h | h | h | h | h | h | h | h | h | h | h) | h
      all_goals cases h
      · exact ⟨24,by decide,rfl⟩
      · exact ⟨16,by decide,rfl⟩
      · exact ⟨8,by decide,rfl⟩
      · exact ⟨0,by decide,rfl⟩
      · exact ⟨200,by decide,rfl⟩
      · exact ⟨192,by decide,rfl⟩
      · exact ⟨184,by decide,rfl⟩
      · exact ⟨176,by decide,rfl⟩
    ) (by simp [outputEffect,Effect.components]) (by simp [outputEffect,Effect.components])
  have saved := state.toSaved.preserve state.toState et.agrees
    (by simp [outputEffect,Effect.components]) (by simp [outputEffect,Effect.components]) (by
      intro target member p len hp
      have targetLow : 312 ≤ target := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      simp only [outputEffect,Effect.components,Write.component,Operand.component,List.map_cons,
        List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
      rcases hp with (h | h | h | h | h | h | h | h | h | h | h | h) | h
      all_goals cases h
      · exact ⟨24,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨16,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨8,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨0,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨200,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨192,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨184,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨176,by decide,Or.inl (by omega),rfl⟩
    )
  have value : Nat256At s (stackPtr s+280) (Arith.uint secret) := by
    rw [show stackPtr s+280 = stackPtr initial-240 from
      stack_address state.toState (off:=280) (by decide)]
    exact state.value
  have limb (j : Nat) (hj : j<4) :
      memLoad s.external (stackPtr s+BitVec.ofNat 64 (280+8*j)) 64 =
        BitVec.ofNat 64 (Arith.uint secret/2^(64*j)) := by
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using value.memLoad_limb j hj
  have makeValue (off : Nat) (bound : off ≤ 520) (extent : 24 ≤ off)
      (words : ∀ j<4, memLoad t.external (stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 (8*j)) 64 =
        BitVec.ofNat 64 (Arith.uint secret/2^(64*j))) :
      Nat256At t (stackPtr initial-BitVec.ofNat 64 off) (Ecdsa.secretValue secret) := by
    rw [secretValue_eq call.argumentsValid]
    apply nat256At_of_memLoad_limbs value.1
    · intro i hi
      exact st.allocated _ ((stack_sub_readable hs (offset:=off) (len:=32)
        (by omega) (by omega)).mem i hi)
    · exact words
  refine ⟨n,t,ht,⟨st,et.rip,saved.pointers,saved.lengths,saved.count,?_,?_,saved.output,saved.capacity⟩⟩
  · apply makeValue 520 (by decide) (by decide)
    intro j hj
    have addr : stackPtr initial-520 = stackPtr s+0 :=
      (stack_address state.toState (off:=0) (by decide)).symm
    simp only [BitVec.ofNat_eq_ofNat] at addr ⊢
    rw [addr]
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,BitVec.add_zero]
    · have h : memLoad t.external (stackPtr s+0) 64 = memLoad s.external (stackPtr s+280) 64 :=
        et.writes.2.2.2.2.2.2.2.1
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h.trans (by
        simpa only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 0 (by decide))
    · exact et.writes.2.2.2.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 1 (by decide))
    · exact et.writes.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 2 (by decide))
    · exact et.writes.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 3 (by decide))
  · apply makeValue 344 (by decide) (by decide)
    intro j hj
    have addr : stackPtr initial-344 = stackPtr s+176 :=
      (stack_address state.toState (off:=176) (by decide)).symm
    simp only [BitVec.ofNat_eq_ofNat] at addr ⊢
    rw [addr]
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
    · exact et.writes.2.2.2.2.2.2.2.2.2.2.2.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 0 (by decide))
    · exact et.writes.2.2.2.2.2.2.2.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 1 (by decide))
    · exact et.writes.2.2.2.2.2.2.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 2 (by decide))
    · exact et.writes.2.2.2.2.2.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero,BitVec.ofNat_eq_ofNat] using limb 3 (by decide))

end P256.Proofs.Signing.Wrapper.Entry.Decode
