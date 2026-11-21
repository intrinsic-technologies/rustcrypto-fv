import Sha3.Proofs.Permutation.RoundMachine.Trace

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs RoundAlgebra Sha3.Spec.Program Keccak

theorem prefixInvariant_model_full {copy : Copy} {initial : RamState} {n : Nat}
    {a : RoundAlgebra.State} {s : RamState}
    (h : PrefixInvariant copy initial n a ⟨257, by decide⟩ s) :
    Models (frameBase initial) (run (roundConstant (n : Int)) a) s := by
  have hm := h.model
  change Models _ (runPrefix _ a 257) s at hm
  rwa [runPrefix_full] at hm

theorem models_run_counter {sp : BitVec 64} {n : Nat} {a : RoundAlgebra.State} {s : RamState}
    (h : Models sp (run (roundConstant (n : Int)) a) s)
    (hc : a.regs 2 = BitVec.ofNat 64 (8 * n)) :
    s.regValue .rdx = BitVec.ofNat 64 (8 * n) := by
  calc
    s.regValue .rdx = read (run (roundConstant (n : Int)) a) (.reg 2) := h (.reg 2) trivial
    _ = (run (roundConstant (n : Int)) a).regs 2 := RoundAlgebra.read.eq_1 _ _
    _ = a.regs 2 := regs_counter_run a (roundConstant (n : Int))
    _ = BitVec.ofNat 64 (8 * n) := hc

theorem models_run_lanes {sp : BitVec 64} {n : Nat} {a : RoundAlgebra.State} {s : RamState}
    (h : Models sp (run (roundConstant (n : Int)) a) s) :
    readLanes sp s = roundLanes (lanes a) (n : Int) :=
  (models_lanes h).trans (lanes_run a (n : Int))

theorem prefixInvariant_rip_full {copy : Copy} {initial : RamState} {n : Nat}
    {a : RoundAlgebra.State} {s : RamState}
    (h : PrefixInvariant copy initial n a ⟨257, by decide⟩ s) :
    s.RIP = (entryAddress copy + 0x4fa : BitVec 64) := by
  have hpc : BitVec.ofNat 64 (dataPc copy (⟨257, by decide⟩ : Fin 258)) =
      entryAddress copy + 0x4fa := by cases copy <;> decide +kernel
  exact h.rip.trans hpc

theorem roundInvariant_prefix_zero {copy : Copy} {initial s : RamState} {n : Nat} {a : Lanes}
    (hn : n < 24) (h : RoundInvariant copy initial n a s)
    (hm : RoundMemory (frameBase initial) s) :
    PrefixInvariant copy initial n (model (frameBase initial) s) 0 s := by
  refine ⟨h.frame, hm, ?_, ?_⟩
  · rw [h.rip, roundPC_lt copy hn]
    cases copy <;> decide +kernel
  · simpa only [Fin.val_zero, runPrefix_zero] using models_model (frameBase initial) s

end Sha3.Proofs.Permutation.RoundMachine
