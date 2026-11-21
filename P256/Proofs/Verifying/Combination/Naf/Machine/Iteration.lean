import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowLoop
import P256.Proofs.Verifying.Combination.Naf.Machine.Progress
import P256.Proofs.Verifying.Combination.Naf.Machine.DigitMachine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open DigitMachine

theorem iteration [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n i k c : Nat} {ds : List Int}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (state : LoopState s t n i k c ds) :
    ∃ fuel u, Advances boundary fuel t u ∧ Progress s u n i := by
  obtain ⟨fuelA,a,runA,stateA,rdxA,rsiA⟩ := window_loop pre input state
  have hi := stateA.indexBound
  have hc := stateA.carryBound
  have branch : BranchPre s a i c (n/2^i%32+c) :=
    ⟨stateA.toFrameState, hi, hc, by omega,
      stateA.r12, stateA.r13, stateA.r14, stateA.r15, stateA.rbp, rdxA, rsiA,
      stateA.outputLength, stateA.outputPointer, stateA.bits, stateA.half,
      stateA.mask, stateA.byteWindow⟩
  by_cases even : (n/2^i%32+c)%2=0
  · have rip : a.RIP=0x10f43f := by simpa only [ite_eq_left even] using stateA.rip
    obtain ⟨fuelB,b,runB,post⟩ := even_branch pre branch rip
    obtain ⟨length,specification⟩ := specification_even hi
      stateA.dsLength stateA.specification even
    exact ⟨fuelA+fuelB,b,runA.trans runB,
      branch_progress pre input stateA post hc (by omega) (by omega) (by omega)
        length specification⟩
  · have odd : (n/2^i%32+c)%2=1 := by omega
    have rip : a.RIP=0x10f470 := by simpa only [ite_eq_right even] using stateA.rip
    have bounds := odd_skip_bounds (by omega : 0<256-i)
      (shifted_bound input.1 (by omega : i≤256)) hc odd
    obtain ⟨fuelB,b,runB,post⟩ := odd_branch pre branch rip bounds.1
    obtain ⟨length,specification⟩ := specification_odd hi input.1 hc
      stateA.dsLength stateA.specification odd
    refine ⟨fuelA+fuelB,b,runA.trans runB,
      branch_progress pre input stateA post (carry_le_one _) (by omega) (by omega)
        (by omega) ?_ ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using length
    · simpa only [List.append_assoc, List.singleton_append] using specification

end P256.Proofs.Verifying.Combination.Naf.Machine
