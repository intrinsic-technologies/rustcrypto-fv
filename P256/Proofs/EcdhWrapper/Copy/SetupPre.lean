import P256.Proofs.EcdhWrapper.Prologue
import P256.Proofs.EcdhWrapper.Copy.Setup

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_address {initial s : RamState}
    (rsp : stackPtr s = stackPtr initial - 504) {off : Nat}
    (member : off ∈ ([32,40] : List Nat)) :
    stackPtr s + BitVec.ofNat 64 off = stackPtr initial - BitVec.ofNat 64 (504-off) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals rw [rsp]; simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

theorem setup_pre [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret, peer] slices)
    (entry : GuardedEntry initial s secret) : SetupPre s := by
  refine ⟨entry.rip, ?_, ?_⟩
  · intro off member
    rw [setup_address entry.rsp member]
    apply writable_of_grow _ entry.agrees.grow
    apply stack_sub_writable8 call.stackAvailable.1
      (fun a ha hp => call_stack_avoids call a ha (.inr hp)) (by
        change 504-off ≤ 4104
        omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro off member offset len bounded
    rw [setup_address entry.rsp member]
    intro i hi j hj eq
    have covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 (504-off)) 8).Covers
        (stackPtr initial - BitVec.ofNat 64 (504-off) + BitVec.ofNat 64 i) := ⟨i,hi,rfl⟩
    have contains := stack_component_within call.stackAvailable.1 (offset := 504-off)
      (by change 504-off ≤ 4104; omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> decide) covered
    apply (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 _ contains
    apply Or.inl
    rw [eq]
    have program := inProgram_of_textOffset (offset+j) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using program

end P256.Proofs.EcdhWrapper.Copy
