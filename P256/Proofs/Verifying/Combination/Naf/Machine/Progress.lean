import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Completion

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open DigitMachine

def Progress [Bindings] (s t : RamState) (n i : Nat) : Prop :=
  (∃ j k c ds, i<j ∧ LoopState s t n j k c ds) ∨ (∃ c ds, Finished s t n c ds)

theorem branch_progress [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {n i c next c' : Nat} {ds added : List Int} {pc : BitVec 64}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (state : LoopState s t n i (i/64) c ds pc)
    (post : BranchPost s t u next c' i added)
    (carryBound : c' ≤ 1) (lower : i < next) (upper : next ≤ i+5) (bound : next ≤ 256)
    (length : (ds++added).length = next)
    (specification : digits n = (ds++added) ++ recode (257-next) (256-next) (n/2^next) c') :
    Progress s u n i := by
  have room : i+added.length ≤ 257 := by
    rw [List.length_append, state.dsLength] at length
    omega
  by_cases more : next < 256
  · exact .inl ⟨next, i/64, c', ds++added, lower,
      branch_loop pre input state post room carryBound (by omega) upper more length specification⟩
  · have last : next=256 := by omega
    rw [last] at post length specification
    exact .inr ⟨c', ds++added, branch_finished pre state post carryBound length specification⟩

theorem loop_of_progress [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n i k c : Nat} {ds : List Int}
    (step : ∀ {v : RamState} {j l d : Nat} {xs : List Int}, LoopState s v n j l d xs →
      ∃ fuel u, Advances boundary fuel v u ∧ Progress s u n j)
    (state : LoopState s t n i k c ds) :
    ∃ fuel u c' ds', Advances boundary fuel t u ∧ Finished s u n c' ds' := by
  generalize remaining : 256-i = count
  induction count using Nat.strongRecOn generalizing t i k c ds with
  | ind count ih =>
    obtain ⟨fuel1, u, run1, progress⟩ := step state
    rcases progress with ⟨j,l,d,xs,larger,next⟩ | ⟨d,xs,done⟩
    · obtain ⟨fuel2, v, c', ds', run2, finished⟩ := ih (256-j)
        (by have := next.indexBound; omega) next rfl
      exact ⟨fuel1+fuel2,v,c',ds',run1.trans run2,finished⟩
    · exact ⟨fuel1,u,d,xs,run1,done⟩

end P256.Proofs.Verifying.Combination.Naf.Machine
