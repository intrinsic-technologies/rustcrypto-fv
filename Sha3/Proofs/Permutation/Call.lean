import Sha3.Proofs.Permutation.Layout
import Sha3.Proofs.Run

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Keccak

def roundLanesPrefix (a : Lanes) (round : Nat) : Lanes :=
  (List.range round).foldl (fun state (i : Nat) ↦ roundLanes state (i : Int)) a

theorem roundLanesPrefix_zero (a : Lanes) : roundLanesPrefix a 0 = a := rfl

theorem roundLanesPrefix_succ (a : Lanes) (round : Nat) :
    roundLanesPrefix a (round + 1) = roundLanes (roundLanesPrefix a round) (round : Int) := by
  simp [roundLanesPrefix, List.range_succ, List.foldl_append]

theorem roundLanesPrefix_24 (a : Lanes) : roundLanesPrefix a 24 = keccakLanes a := rfl

theorem rounds_advance_of_step [Bindings] (copy : Copy) (boundary : ReturnBoundary) (code : CodeMap)
    (initial : RamState) (a : Lanes) (fuel : Nat)
    (body : ∀ round, round < 24 → ∀ state,
      AdvanceTriple boundary fuel (RoundInvariant copy initial round state) code
        (fun _ s ↦ RoundInvariant copy initial (round + 1) (roundLanes state (round : Int)) s)) :
    AdvanceTriple boundary (24 * fuel) (RoundInvariant copy initial 0 a) code
      (fun _ s ↦ RoundInvariant copy initial 24 (keccakLanes a) s) := by
  have h := AdvanceTriple.iterate (boundary := boundary) (code := code)
    (invariant := fun round ↦ RoundInvariant copy initial round (roundLanesPrefix a round)) 24 fuel
    (fun round hround ↦ by
      simpa only [roundLanesPrefix_succ] using body round hround (roundLanesPrefix a round))
  exact h

theorem CallFrame.readable {initial s : RamState} (h : CallFrame initial s)
    {address : BitVec 64} {bytes : Nat} (hr : MemReadable initial address bytes) :
    MemReadable s address bytes :=
  ⟨hr.low, fun i hi ↦ h.grows _ (hr.mem i hi)⟩

end Sha3.Proofs.Permutation
