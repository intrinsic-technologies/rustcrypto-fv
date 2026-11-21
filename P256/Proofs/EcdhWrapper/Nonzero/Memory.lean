import P256.Proofs.EcdhWrapper.Scalar.Call
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def clobbers (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.flags,.rip,
    .mem (stackPtr s-312) 8,.mem (stackPtr s-320) 8,.mem (stackPtr s-328) 8,
    .mem (stackPtr s-336) 8,.mem (stackPtr s-512) 8,.mem (stackPtr s-520) 8,
    .mem (stackPtr s-528) 8,.mem (stackPtr s-513) 1]

theorem writes {initial : RamState} (stack : Stack.Valid initial 4104) :
    WritesWithin (clobbers initial) #v[ScalarFrame.Work.region initial 4104 304] := by
  have bounds := stack_bounds stack
  have contains (off len : Nat) (lo : off ≤ 4104) (hi : len+304 ≤ off)
      {a : BitVec 64} (cover : (Component.mem (stackPtr initial-BitVec.ofNat 64 off) len).Covers a) :
      (ScalarFrame.Work.region initial 4104 304).Contains a.toNat := by
    obtain ⟨i,hi',rfl⟩ := cover
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^64),
      Nat.mod_eq_of_lt (by rw [stack_sub_toNat stack lo]; omega),stack_sub_toNat stack lo]
    change (stackPtr initial).toNat-4104 ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-304)
    constructor <;> omega
  intro c hc a cover
  simp only [clobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals exact ⟨_,by simp,contains _ _ (by decide) (by decide) cover⟩

theorem loaded_after [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (g : AgreesExcept (clobbers initial) s t) (loaded : ProgramLoaded s) : ProgramLoaded t := by
  have frame := g.memoryWriteFrame (writes call.stackAvailable.1)
  intro a b hb
  rw [frame a]
  · exact loaded a b hb
  · intro region hr hin
    have eq : region = ScalarFrame.Work.region initial 4104 304 := by simpa using hr
    subst region
    apply call_stack_avoids call a ?_ (.inl ⟨b,hb⟩)
    have bounds := stack_bounds (show Stack.Valid initial 4104 from call.stackAvailable.1)
    change (stackPtr initial).toNat-4104 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat-4104+(4104-304) at hin
    change (stackPtr initial).toNat-4104 ≤ a.toNat ∧
      a.toNat < (Stack.region initial 4104).start+(Stack.region initial 4104).size
    rw [stack_region_end]
    constructor <;> omega

theorem scalar_preserved {initial s t : RamState}
    (stack : Stack.Valid initial 4104) (g : AgreesExcept (clobbers initial) s t)
    {x : Nat} (value : SecretKeyFromBytes.Scalar.Nat256At s (stackPtr initial-264) x) :
    SecretKeyFromBytes.Scalar.Nat256At t (stackPtr initial-264) x := by
  have frame := g.memoryWriteFrame (writes stack)
  refine ⟨value.1,fun i hi => ?_⟩
  rw [frame _]
  · exact value.2 i hi
  · intro region hr hin
    have eq : region = ScalarFrame.Work.region initial 4104 304 := by simpa using hr
    subst region
    have bounds := stack_bounds stack
    have low : (stackPtr initial-264).toNat = (stackPtr initial).toNat-264 :=
      stack_sub_toNat stack (offset := 264) (by decide)
    change _ ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-304) at hin
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^64),
      Nat.mod_eq_of_lt (by rw [low]; omega),low] at hin
    omega

end P256.Proofs.EcdhWrapper.Nonzero
