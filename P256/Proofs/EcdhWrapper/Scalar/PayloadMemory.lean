import P256.Proofs.EcdhWrapper.Scalar.Copies
import P256.Proofs.EcdhWrapper.Scalar.Validity

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program.ScalarFrame SecretKeyFromBytes.Scalar

def payloadClobbers (initial : RamState) : List Component :=
  Nonzero.clobbers initial ++ [.mem (stackPtr initial-192) 32,.mem (stackPtr initial-160) 32]

theorem payload_writes {initial : RamState} (stack : Stack.Valid initial 4104) :
    WritesWithin (payloadClobbers initial) (wrapperRegions ecdhDiffieHellman initial) := by
  intro c hc a cover
  simp only [payloadClobbers,Nonzero.clobbers,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  all_goals try exact cover.elim
  all_goals refine ⟨callStack ecdhDiffieHellman initial,by simp [wrapperRegions],?_⟩
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 312) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 320) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 328) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 336) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 512) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 520) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 528) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 513) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 192) (by decide) (by decide) cover
  · exact stack_component_within (routine := ecdhDiffieHellman) stack (offset := 160) (by decide) (by decide) cover

theorem first_copy_agrees {initial s t : RamState}
    (rsp : stackPtr s = stackPtr initial-504) (effect : (FirstCopy.effect s).Holds s t) :
    AgreesExcept (payloadClobbers initial) s t := by
  have destination : FirstCopy.destination s = stackPtr initial-192 := by
    change stackPtr s+312 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  apply effect.agrees.widen
  · intro c hc hm
    simp only [FirstCopy.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [payloadClobbers,Nonzero.clobbers]
    all_goals simp [Component.isMem] at hm
  · intro a c hc cover
    simp only [FirstCopy.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨i,hi,rfl⟩ := cover
    all_goals refine ⟨.mem (stackPtr initial-192) 32,by simp [payloadClobbers],?_⟩
    · exact ⟨i,by omega,by rw [destination]⟩
    · exact ⟨8+i,by omega,by rw [destination,BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i,by omega,by rw [destination,BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i,by omega,by rw [destination,BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩

theorem second_copy_agrees {initial s t : RamState}
    (rsp : stackPtr s = stackPtr initial-504)
    (effect : (Copy32.effect 0x1069b6 SecondCopy.source SecondCopy.destination s).Holds s t) :
    AgreesExcept (payloadClobbers initial) s t := by
  have destination : SecondCopy.destination s = stackPtr initial-160 := by
    change stackPtr s+344 = _
    rw [rsp]; simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have g := Copy32.frame effect
  rw [destination] at g
  exact g.mono (by simp [Copy32.components,payloadClobbers,Nonzero.clobbers])

theorem validity_scalar {initial s t : RamState} {x : Nat}
    (stack : Stack.Valid initial 4104) (g : AgreesExcept (Nonzero.clobbers initial) s t)
    (value : Nat256At s (stackPtr initial-192) x) :
    Nat256At t (stackPtr initial-192) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  rw [g.byte]
  · exact value.2 i hi
  · intro c hc cover
    simp only [Nonzero.clobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨j,hj,eq⟩ := cover
    all_goals
      exact stack_sub_apart stack (by decide) (b := 192) (by decide)
        (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm

theorem payload_word {initial s t : RamState}
    (stack : Stack.Valid initial 4104) (g : AgreesExcept (payloadClobbers initial) s t)
    {offset : Nat} (kept : offset ≤ 48 ∨ offset=464 ∨ offset=472) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart g
  intro address len member
  have cases : (address=stackPtr initial-312 ∧ len=8) ∨
      (address=stackPtr initial-320 ∧ len=8) ∨ (address=stackPtr initial-328 ∧ len=8) ∨
      (address=stackPtr initial-336 ∧ len=8) ∨ (address=stackPtr initial-512 ∧ len=8) ∨
      (address=stackPtr initial-520 ∧ len=8) ∨ (address=stackPtr initial-528 ∧ len=8) ∨
      (address=stackPtr initial-513 ∧ len=1) ∨ (address=stackPtr initial-192 ∧ len=32) ∨
      (address=stackPtr initial-160 ∧ len=32) := by
    simpa [payloadClobbers,Nonzero.clobbers] using member
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact stack_sub_apart stack (a := 312) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 320) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 328) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 336) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 512) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 520) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 528) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 513) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 192) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)
  · exact stack_sub_apart stack (a := 160) (b := offset) (by decide) (by omega)
      (by decide) (by omega) (by omega)

end P256.Proofs.EcdhWrapper.Scalar
