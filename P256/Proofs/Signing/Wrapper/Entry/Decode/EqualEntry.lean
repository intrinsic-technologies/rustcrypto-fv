import P256.Proofs.Signing.Wrapper.Entry.Decode.Valid
import P256.Proofs.Signing.Wrapper.Entry.Decode.ZeroPrepare
import P256.Proofs.Signing.Wrapper.Entry.Decode.EqualArguments

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure EqualEntry [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520, Saved initial s where
  rip : s.RIP = 0x1025d4
  left : s.regValue .rdi = stackPtr initial-240
  right : s.regValue .rdx = stackPtr initial-344
  leftLength : s.regValue .rsi = 4
  rightLength : s.regValue .rcx = 4
  value : Nat256At s (stackPtr initial-240) (Arith.uint secret)
  zero : Nat256At s (stackPtr initial-344) 0

theorem equal_entry [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : ValidState initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ EqualEntry initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨n,a,ha,ra,_,ea⟩ := zeroPrepare_correct (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x256a zeroPrepareBytes
      (by decide) (by decide +kernel))
    (block_pre call state.toState state.rip (by simp) (by simp))
  have sa := after_stack call state.toState ha ra ea.agrees
    (by
      intro p len hp
      simp only [zeroPrepareEffect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
      rcases hp with (h | h | h | h | h | h | h | h) | h
      all_goals cases h
      · exact ⟨280,by decide,rfl⟩
      · exact ⟨288,by decide,rfl⟩
      · exact ⟨296,by decide,rfl⟩
      · exact ⟨304,by decide,rfl⟩
      · exact ⟨200,by decide,rfl⟩
      · exact ⟨192,by decide,rfl⟩
      · exact ⟨184,by decide,rfl⟩
      · exact ⟨176,by decide,rfl⟩
    ) (by simp [zeroPrepareEffect,Effect.components]) (by simp [zeroPrepareEffect,Effect.components])
  have saved := state.toSaved.preserve state.toState ea.agrees
    (by simp [zeroPrepareEffect,Effect.components]) (by simp [zeroPrepareEffect,Effect.components]) (by
      intro target member p len hp
      simp only [zeroPrepareEffect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
      have targetLow : 312 ≤ target := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide
      rcases hp with (h | h | h | h | h | h | h | h) | h
      all_goals cases h
      · exact ⟨280,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨288,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨296,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨304,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨200,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨192,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨184,by decide,Or.inl (by omega),rfl⟩
      · exact ⟨176,by decide,Or.inl (by omega),rfl⟩
    )
  have allocated (off : Nat) (bound : off ≤ 520) (extent : 24 ≤ off) :
      ∀ i < 32, (a.external[stackPtr initial-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    exact sa.allocated _ ((stack_sub_readable hs (offset:=off) (len:=32)
      (by omega) (by omega)).mem i hi)
  have value : Nat256At a (stackPtr initial-240) (Arith.uint secret) := by
    apply nat256At_of_memLoad_limbs
    · exact Nat.lt_trans ((arguments_iff secret message).mp call.argumentsValid).2.2
        (by decide +kernel : Operations.domain.n < 2^256)
    · exact allocated 240 (by decide) (by decide)
    · intro j hj
      have addr : stackPtr initial-240 = stackPtr s+280 := (stack_address state.toState (off:=280) (by decide)).symm
      rw [addr]
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      all_goals simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
      · exact ea.writes.1.trans state.word0
      · exact ea.writes.2.1.trans state.word1
      · exact ea.writes.2.2.1.trans state.word2
      · exact ea.writes.2.2.2.1.trans state.word3
  have zero : Nat256At a (stackPtr initial-344) (0) := by
    apply nat256At_of_memLoad_limbs
    · decide
    · exact allocated 344 (by decide) (by decide)
    · intro j hj
      have addr : stackPtr initial-344 = stackPtr s+176 := (stack_address state.toState (off:=176) (by decide)).symm
      rw [addr]
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      all_goals simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,Nat.zero_div]
      · exact ea.writes.2.2.2.2.2.2.2
      · exact ea.writes.2.2.2.2.2.2.1
      · exact ea.writes.2.2.2.2.2.1
      · exact ea.writes.2.2.2.2.1
  obtain ⟨m,t,ht,rt,_,et⟩ := equal_arguments (returnBoundary initial) outside a ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x25ba equalArgumentBytes
      (by decide) (by decide +kernel)) ea.rip
  have st := after_stack call sa ht rt et.agrees
    (by simp [equalArgumentEffect,Effect.components])
    (by simp [equalArgumentEffect,Effect.components]) (by simp [equalArgumentEffect,Effect.components])
  have mem := et.agrees.external (by simp [equalArgumentEffect,Effect.components,Component.Covers])
  refine ⟨n+m,t,ha.trans ht,⟨st,?_,et.rip,?_,?_,et.writes.2.2.1,et.writes.2.2.2,?_,?_⟩⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (et.agrees.read (n:=64) (r:=12) (by simp [equalArgumentEffect,Effect.components])).trans saved.pointers
    · exact (et.agrees.read (n:=64) (r:=13) (by simp [equalArgumentEffect,Effect.components])).trans saved.count
    · simpa only [mem] using saved.lengths
    · simpa only [mem] using saved.output
    · simpa only [mem] using saved.capacity
  · exact et.writes.1.trans (stack_address sa (by decide))
  · exact et.writes.2.1.trans (stack_address sa (by decide))
  · simpa only [Nat256At,mem] using value
  · simpa only [Nat256At,mem] using zero

end P256.Proofs.Signing.Wrapper.Entry.Decode
