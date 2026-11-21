import P256.Proofs.Nonce.Update.Absorb.Prefix.Buffer
import P256.Proofs.Nonce.Update.Absorb.Prefix.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}

theorem source_eq (input : Entered initial s state) :
    source s = initial.regValue .rdi + 32 := input.valuePointer

theorem destination_eq (input : Entered initial s state) :
    destination s = stackPtr s + 152 := by
  change s.regValue .r14 = _
  rw [input.bufferPointer, input.rsp]
  rfl

theorem destination_sub (input : Entered initial s state) :
    destination s = stackPtr initial - 528 := by
  rw [destination_eq input]
  exact ScalarFrame.scalar_stack_address input.rsp (by decide) (by decide)

theorem block_pre (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Entered initial s state) : Pre s := by
  refine ⟨input.rip, input.position, ?_, ?_, ?_, ?_⟩
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [source_eq input]
    rcases member with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      state_readable pre input.toFrameState (by decide)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [destination_eq input]
    rcases member with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      stack_writable8 pre input.toFrameState (by decide) (by decide)
  · intro offset member codeOffset codeLen codeBound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [destination_eq input]
    rcases member with rfl | rfl | rfl | rfl
    all_goals simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) codeBound
  · intro first firstMember second secondMember i hi j hj eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
    obtain ⟨firstOffset, firstEq, firstBound⟩ :
        ∃ off : Nat, first = BitVec.ofNat 64 off ∧ off ≤ 24 := by
      rcases firstMember with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl, by decide⟩
      · exact ⟨8, rfl, by decide⟩
      · exact ⟨16, rfl, by decide⟩
      · exact ⟨24, rfl, by decide⟩
    obtain ⟨secondOffset, secondEq, secondBound⟩ :
        ∃ off : Nat, second = BitVec.ofNat 64 off ∧ off ≤ 24 := by
      rcases secondMember with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl, by decide⟩
      · exact ⟨8, rfl, by decide⟩
      · exact ⟨16, rfl, by decide⟩
      · exact ⟨24, rfl, by decide⟩
    have dstInside : (Stack.region initial 1856).Contains
        (destination s + first + BitVec.ofNat 64 i).toNat := by
      rw [destination_sub input, firstEq, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ScalarFrame.stack_contains pre.callee (offset := 528) (len := 32) (by decide) (by decide) ⟨firstOffset + i, by omega, rfl⟩
    have srcInside : (registerRegion initial .rdi 64).Contains
        (source s + second + BitVec.ofNat 64 j).toNat := by
      rw [source_eq input, secondEq]
      change (registerRegion initial .rdi 64).Contains
        (initial.regValue .rdi + BitVec.ofNat 64 32 + BitVec.ofNat 64 secondOffset + BitVec.ofNat 64 j).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      apply ScalarFrame.output_contains pre.callee (offset := 32 + secondOffset) (len := 8) (by omega)
      exact ⟨j, hj, by simp only [BitVec.ofNat_add, BitVec.add_assoc]⟩
    exact pre.separation _ srcInside (eq ▸ dstInside)

end P256.Proofs.Nonce.Update.Absorb.Prefix.Buffer
