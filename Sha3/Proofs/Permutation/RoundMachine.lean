import Sha3.Proofs.Permutation.RoundMachine.Finish
import Sha3.Proofs.Permutation.RoundMachine.Instructions

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program Keccak

theorem round_advance [Bindings] (copy : Copy) {boundary : ReturnBoundary} {initial : RamState}
    {n : Nat} {a : Lanes} (hn : n < 24) (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 260
      (fun s ↦ RoundInvariant copy initial n a s ∧ RoundMemory (frameBase initial) s)
      Extracted.programImage
      (fun _ t ↦ RoundInvariant copy initial (n + 1) (roundLanes a (n : Int)) t ∧
        RoundMemory (frameBase initial) t) := by
  intro s hready hcode hp
  let m := model (frameBase initial) s
  have hm : Models (frameBase initial) m s := models_model _ _
  have hc : m.regs 2 = BitVec.ofNat 64 (8 * n) := hp.1.counter
  have hpre : PrefixInvariant copy initial n m 0 s := roundInvariant_prefix_zero hn hp.1 hp.2
  obtain ⟨t, hrun, hready', hcode', ht⟩ :=
    prefix_advance copy hn hc hb (dataSteps copy) (⟨257, by decide⟩ : Fin 258) s hready hcode hpre
  have hmodel := prefixInvariant_model_full ht
  have hcounter := models_run_counter hmodel hc
  have hip := prefixInvariant_rip_full ht
  have hlanes : readLanes (frameBase initial) t = roundLanes a (n : Int) := by
    have hl := models_run_lanes hmodel
    have hi : lanes m = a := (models_lanes hm).symm.trans hp.1.lanes
    rwa [hi] at hl
  obtain ⟨u, hcontrol, hready'', hcode'', he⟩ :=
    control_advance_image copy hb hn t hready' hcode' ⟨hip, hcounter⟩
  exact ⟨u, hrun.trans hcontrol, hready'', hcode'',
    controlEffect_roundInvariant he ht.frame hlanes, ht.memory.of_holds he⟩

end Sha3.Proofs.Permutation.RoundMachine
