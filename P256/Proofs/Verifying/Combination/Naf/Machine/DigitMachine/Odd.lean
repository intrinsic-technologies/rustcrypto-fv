import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.OddSelect
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.OddSkip
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.Padding
import P256.Proofs.Verifying.Combination.Naf.Machine.BranchLoop
import P256.Proofs.Verifying.Combination.Naf.Machine.RecodeBranchMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

set_option maxHeartbeats 600000 in
theorem odd_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary} {i c w : Nat}
    (pre : Pre s boundary) (state : BranchPre s t i c w) (rip : t.RIP = 0x10f470)
    (positive : 0<skip (256-i) w) :
    ∃ fuel u, Advances boundary fuel t u ∧
      BranchPost s t u (i+skip (256-i) w) (carry w) i
        (digit w :: List.replicate (skip (256-i) w-1) 0) := by
  let k := skip (256-i) w
  have pos : 0<k := positive
  have small : k≤5 := Nat.min_le_left _ _
  have bound : i+k ≤ 256 := by
    have hk : k ≤ 256-i := Nat.le_trans (Nat.min_le_right 5 (256-i-carry w)) (Nat.sub_le _ _)
    have hi := state.indexBound
    omega
  obtain ⟨na, a, ra, fa, ipA, axA, r13A, dxA, ga⟩ := odd_select pre state rip
  have siA : a.regValue .rsi = s.regValue .rdi :=
    (ga.read (n := 64) (r := 6) (by simp)).trans state.rsi
  have r14A : a.regValue .r14 = BitVec.ofNat 64 i :=
    (ga.read (n := 64) (r := 14) (by simp)).trans state.r14
  obtain ⟨b, rb, fb, ipB, firstB, gb, mb⟩ :=
    DigitStore.digit_store pre fa ipA siA r14A state.indexBound dxA
  have memoryB : MemoryWriteFrame t b #v[digitRegion s i 1] := by
    intro address ha
    rw [mb address ha, ga.external (by simp [Component.Covers])]
  have bitsB : memLoad b.external (stackPtr b+24) 64 = 256 := by
    rw [show stackPtr b+24 = stackPtr s-112 from stack_address fb.rsp (by decide)]
    exact (branch_stack_read pre (by have := state.indexBound; omega) memoryB
      (by decide : 112≤168) (by decide)).trans state.bits
  have early := ga.trans gb
  have r12B : b.regValue .r12 = 5 := (early.read (n := 64) (r := 12) (by simp)).trans state.r12
  have r13B : b.regValue .r13 = BitVec.ofNat 64 (carry w) :=
    (gb.read (n := 64) (r := 13) (by simp)).trans r13A
  have bpB : b.regValue .rbp = -BitVec.ofNat 64 i :=
    (early.read (n := 64) (r := 5) (by simp)).trans state.rbp
  obtain ⟨nc, q, rc, fq, ipQ, bpQ, cfQ, gq⟩ :=
    odd_skip pre fb state.indexBound ipB r12B r13B bpB bitsB
  have middle := early.trans gq
  have r14Q : q.regValue .r14 = BitVec.ofNat 64 i :=
    (middle.read (n := 64) (r := 14) (by simp)).trans state.r14
  have siQ : q.regValue .rsi = s.regValue .rdi :=
    (middle.read (n := 64) (r := 6) (by simp)).trans state.rsi
  have axQ : q.regValue .rax = BitVec.ofNat 64 (257-i) :=
    ((gb.trans gq).read (n := 64) (r := 0) (by simp)).trans axA
  obtain ⟨nd, d, rd, fd, ipD, r14D, zeroesD, gd⟩ :=
    padding pre fq bound pos small ipQ cfQ r14Q bpQ siQ axQ
  have memoryQ : MemoryWriteFrame t q #v[digitRegion s i 1] := by
    intro address ha
    rw [gq.external (by simp [Component.Covers])]
    exact memoryB address ha
  have memoryQD : MemoryWriteFrame q d #v[digitRegion s (i+1) (k-1)] :=
    (output_after pre fq (i := i+1) (len := k-1) (by omega)
      (readyToStep fd.machine fd.bindingsSupported) gd
      (by simp [Component.Covers]) (by simp)).2
  have firstQ : q.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
      some (UInt8.ofNat (BitVec.ofInt 8 (digit w)).toNat) := by
    rw [gq.external (by simp [Component.Covers])]
    exact firstB
  have bytesD := append_padding pre bound pos firstQ zeroesD memoryQD
  have memoryD := slice_frame_trans pre bound pos memoryQ memoryQD
  have r15D : d.regValue .r15 = BitVec.ofNat 64 i :=
    ((middle.trans gd).read (n := 64) (r := 15) (by simp)).trans state.r15
  have bpD : d.regValue .rbp = BitVec.ofNat 64 k :=
    (gd.read (n := 64) (r := 5) (by simp)).trans bpQ
  have bitsD : memLoad d.external (stackPtr d+24) 64 = 256 := by
    rw [show stackPtr d+24 = stackPtr s-112 from stack_address fd.rsp (by decide)]
    exact (branch_stack_read pre (by omega) memoryD (by decide : 112≤168) (by decide)).trans state.bits
  obtain ⟨ne, u, re, fu, ipU, r15U, bpU, gu⟩ := BranchTail.tail pre fd bound ipD r15D bpD bitsD
  have full := (middle.trans gd).trans gu
  refine ⟨_, u, (((ra.trans rb).trans rc).trans rd).trans re,
    ⟨fu, ipU, ?_, ?_, ?_, r15U, bpU, ?_, ?_⟩⟩
  · exact (full.read (n := 64) (r := 12) (by simp)).trans state.r12
  · exact ((((gb.trans gq).trans gd).trans gu).read (n := 64) (r := 13) (by simp)).trans r13A
  · exact (gu.read (n := 64) (r := 14) (by simp)).trans r14D
  · intro j hj
    rw [gu.external (by simp [Component.Covers])]
    exact bytesD j hj
  · have length : (digit w :: List.replicate (k-1) 0).length = k := by
      simp only [List.length_cons, List.length_replicate]
      omega
    change MemoryWriteFrame t u #v[digitRegion s i (digit w :: List.replicate (k-1) 0).length]
    rw [length]
    intro address ha
    rw [gu.external (by simp [Component.Covers])]
    exact memoryD address ha

end P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine
