import P256.Proofs.EcdhWrapper.Scalar.FirstCopy
import P256.Proofs.EcdhWrapper.Scalar.SecondCopy
import P256.Proofs.EcdhWrapper.Scalar.CopyMemory
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem FirstCopy.value {s t : RamState} {x : Nat}
    (h : (FirstCopy.effect s).Holds s t) (input : Nat256At s (FirstCopy.source s) x)
    (allocated : ∀ i < 32, (t.external[FirstCopy.destination s+BitVec.ofNat 64 i]?).isSome) :
    Nat256At t (FirstCopy.destination s) x := by
  apply nat256At_of_memLoad_limbs input.1 allocated
  intro j hj
  have eq : memLoad t.external (FirstCopy.destination s+BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (FirstCopy.source s+BitVec.ofNat 64 (8*j)) 64 := by
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h0 : memLoad t.external (FirstCopy.destination s) 64 =
          memLoad s.external (FirstCopy.source s) 64 := h.writes.2.2.1
      simpa only [Nat.mul_zero,BitVec.add_zero] using h0
    · exact h.writes.2.2.2.1
    · exact h.writes.2.2.2.2.1
    · exact h.writes.2.2.2.2.2
  exact eq.trans (input.memLoad_limb j hj)

theorem first_copy [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {x : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x106923) (rsp : stackPtr s = stackPtr initial-504)
    (scalar : Nat256At s (stackPtr initial-264) x) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      (FirstCopy.effect s).Holds s t ∧ Nat256At t (stackPtr initial-192) x := by
  have pre : Copy32.Pre 0x106923 FirstCopy.source FirstCopy.destination s :=
    stack_copy_pre call grow rsp rip (src := 240) (dst := 312)
      (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)
  obtain ⟨fuel,t,run,readyT,_,effect⟩ := FirstCopy.copy (returnBoundary initial) outside s
    ready (FirstCopy.loaded loaded) pre
  have source : FirstCopy.source s = stackPtr initial-264 := by
    change stackPtr s+240 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have destination : FirstCopy.destination s = stackPtr initial-192 := by
    change stackPtr s+312 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have readable : MemReadable t (FirstCopy.destination s) 32 := by
    rw [destination]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 192) (len := 32) (by decide) (by decide))
      (fun a ha => effect.agrees.grow a (grow a ha))
  refine ⟨fuel,t,run,readyT,effect,?_⟩
  rw [← destination]
  exact FirstCopy.value effect (source ▸ scalar) readable.mem

theorem second_copy [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {x : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x106976) (rsp : stackPtr s = stackPtr initial-504)
    (scalar : Nat256At s (stackPtr initial-192) x) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      (Copy32.effect 0x1069b6 SecondCopy.source SecondCopy.destination s).Holds s t ∧
      Nat256At t (stackPtr initial-160) x := by
  have pre : Copy32.Pre 0x106976 SecondCopy.source SecondCopy.destination s :=
    stack_copy_pre call grow rsp rip (src := 312) (dst := 344)
      (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)
  obtain ⟨fuel,t,run,readyT,_,effect⟩ := SecondCopy.copy (returnBoundary initial) outside s
    ready (SecondCopy.loaded loaded) pre
  have source : SecondCopy.source s = stackPtr initial-192 := by
    change stackPtr s+312 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have destination : SecondCopy.destination s = stackPtr initial-160 := by
    change stackPtr s+344 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have input : MemReadable s (SecondCopy.source s) 32 := by
    rw [source]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 192) (len := 32) (by decide) (by decide)) grow
  have output : MemReadable t (SecondCopy.destination s) 32 := by
    rw [destination]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 160) (len := 32) (by decide) (by decide))
      (fun a ha => effect.agrees.grow a (grow a ha))
  have copied := Copy32.copy_bytes effect input output
  rw [source,destination] at copied
  exact ⟨fuel,t,run,readyT,effect,⟨scalar.1,fun i hi => (copied i hi).trans (scalar.2 i hi)⟩⟩

end P256.Proofs.EcdhWrapper.Scalar
