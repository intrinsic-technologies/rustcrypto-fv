import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.BranchLoop
import P256.Proofs.Verifying.Combination.Naf.Machine.Finish

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open DigitMachine

structure Finished [Bindings] (s t : RamState) (n c : Nat) (ds : List Int) : Prop
    extends FrameState s t where
  rip : t.RIP = 0x10f4da
  carryBound : c ≤ 1
  length : ds.length = 256
  specification : digits n = ds ++ if c=0 then [] else [1]
  output : DigitsAt t (s.regValue .rdi) ds
  r13 : t.regValue .r13 = BitVec.ofNat 64 c
  r14 : t.regValue .r14 = BitVec.ofNat 64 ds.length
  outputLength : memLoad t.external (stackPtr s-136) 64 = 257
  outputPointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi

theorem branch_finished [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {n i c c' : Nat} {ds added : List Int} {pc : BitVec 64}
    (pre : Pre s boundary) (state : LoopState s t n i (i/64) c ds pc)
    (post : BranchPost s t u 256 c' i added) (carryBound : c' ≤ 1)
    (length : (ds++added).length = 256)
    (specification : digits n = (ds++added) ++ recode (257-256) (256-256) (n/2^256) c') :
    Finished s u n c' (ds++added) := by
  have room : i+added.length ≤ 257 := by
    have h := state.dsLength
    rw [List.length_append, h] at length
    omega
  refine ⟨post.toFrameState, ?_, carryBound, length, ?_,
    post.output pre state.dsLength room state.output, post.r13, ?_, ?_, ?_⟩
  · simpa only [show ¬256<256 from by decide, ite_false] using post.rip
  · simpa only [show 257-256=1 from rfl, show 256-256=0 from rfl, recode, ite_true] using specification
  · rw [length]
    exact post.r14
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.outputLength
  · exact (branch_stack_read pre room post.memory (by decide) (by decide)).trans state.outputPointer

theorem Finished.digits_length [Bindings] {s t : RamState} {n c : Nat} {ds : List Int}
    (state : Finished s t n c ds) : (digits n).length = ds.length+c := by
  rw [state.specification, List.length_append]
  have hc := state.carryBound
  by_cases zero : c=0
  · simp [zero]
  · have one : c=1 := by omega
    simp [one]


theorem Finished.correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n c : Nat} {ds : List Int} (pre : Pre s boundary) (state : Finished s t n c ds)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 257 168 ∧
      u.regValue .rax = BitVec.ofNat 64 (digits n).length ∧
      DigitsAt u (s.regValue .rdi) (digits n) := by
  obtain ⟨u, result, value, output⟩ := finish_recoding pre state.toFrameState state.rip
    state.carryBound (by rw [state.length]; omega) state.r13 state.r14 state.outputLength
    state.outputPointer state.output execution
  refine ⟨u, result, ?_, ?_⟩
  · simpa only [state.digits_length] using value
  · rw [state.specification]
    exact output

end P256.Proofs.Verifying.Combination.Naf.Machine
