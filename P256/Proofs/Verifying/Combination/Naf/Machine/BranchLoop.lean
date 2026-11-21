import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine.State
import P256.Proofs.Verifying.Combination.Naf.Invariant

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open DigitMachine

theorem branch_output_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {i count : Nat} (pre : Pre s boundary) (room : i+count ≤ 257)
    (memory : MemoryWriteFrame t u #v[digitRegion s i count]) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 257] := by
  intro a ha
  apply memory a
  intro region hr hin
  have eq : region = digitRegion s i count := by simpa using hr
  subst region
  apply ha (registerRegion s .rdi 257) (by simp)
  have bounded : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
  change (s.regValue .rdi+BitVec.ofNat 64 i).toNat ≤ a.toNat ∧
    a.toNat < (s.regValue .rdi+BitVec.ofNat 64 i).toNat+count at hin
  rw [toNat_add_ofNat _ _ (by omega)] at hin
  change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat+257
  constructor <;> omega

theorem branch_stack_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {i count offset width : Nat} (pre : Pre s boundary) (room : i+count ≤ 257)
    (memory : MemoryWriteFrame t u #v[digitRegion s i count])
    (ho : offset ≤ 168) (hl : width/8 ≤ offset) :
    memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) width =
      memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) width := by
  have frame := branch_output_frame pre room memory
  apply memLoad_congr
  intro j hj
  have byte : u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 j]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 j]? := by
    apply frame
    intro region hr hin
    have eq : region = registerRegion s .rdi 257 := by simpa using hr
    subst region
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    exact ScalarFrame.stack_contains pre.toCalleePre ho (by omega) ⟨j,hj,rfl⟩
  exact congrArg (fun byte : Option UInt8 => byte.getD 0) byte

theorem branch_iterator [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {i count n k : Nat} (pre : Pre s boundary) (room : i+count ≤ 257)
    (memory : MemoryWriteFrame t u #v[digitRegion s i count])
    (iterator : Iterator.StateAt t (stackPtr s-88) (s.regValue .rdx) n k) :
    Iterator.StateAt u (stackPtr s-88) (s.regValue .rdx) n k := by
  have read (offset : Nat) (ho : 8 ≤ offset ∧ offset ≤ 168) :
      memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) 64 :=
    branch_stack_read pre room memory ho.2 (by omega)
  have addr (a o : BitVec 64) : a-88+o = a-(88-o) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  constructor
  · exact (read 88 (by decide)).trans iterator.pointer
  · rw [addr]
    exact (read 80 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using iterator.remaining)
  · rw [addr]
    exact (read 72 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using iterator.index)
  · rw [addr]
    exact (read 64 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using iterator.low)
  · rw [addr]
    exact (read 56 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using iterator.high)

theorem DigitMachine.BranchPost.output [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {i next c : Nat} {ds added : List Int} (pre : Pre s boundary)
    (post : BranchPost s t u next c i added) (length : ds.length = i)
    (room : i+added.length ≤ 257) (output : DigitsAt t (s.regValue .rdi) ds) :
    DigitsAt u (s.regValue .rdi) (ds++added) := by
  apply output_append_segment output
  · have bound : (s.regValue .rdi).toNat+257 < 2^32 := pre.outputBounded
    omega
  · omega
  · rw [length]
    simpa only [UInt8.ofNat_bitVecToNat] using post.bytes
  · rw [length]
    exact post.memory

theorem branch_loop [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {n i c next c' : Nat} {ds added : List Int} {pc : BitVec 64}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (state : LoopState s t n i (i/64) c ds pc)
    (post : BranchPost s t u next c' i added)
    (room : i+added.length ≤ 257) (carryBound : c' ≤ 1)
    (lower : i ≤ next) (upper : next ≤ i+5) (nextBound : next < 256)
    (length : (ds++added).length = next)
    (specification : digits n = (ds++added) ++ recode (257-next) (256-next) (n/2^next) c') :
    LoopState s u n next (i/64) c' (ds++added) := by
  refine ⟨post.toFrameState, ?_, nextBound, carryBound, iterator_index_step lower upper,
    length, specification, source_preserved pre post.toFrameState input,
    post.output pre state.dsLength room state.output,
    branch_iterator pre room post.memory state.iterator,
    post.r12, post.r13, post.r14, post.r15, post.rbp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_eq_left nextBound] using post.rip
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.outputLength
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.outputPointer
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.bits
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.half
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.mask
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.byteWindow

end P256.Proofs.Verifying.Combination.Naf.Machine
