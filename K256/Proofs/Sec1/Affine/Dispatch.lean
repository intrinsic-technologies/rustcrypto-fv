import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Sec1.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

private theorem registers_eq {a b : Values Value Reg.count}
    (same : ∀ i : Fin 53, a[i.val] = b[i.val]) : a = b :=
  Vector.ext fun i hi => same ⟨i, hi⟩

local macro "dispatch_regs" : tactic => `(tactic| (
  congr 2
  apply registers_eq
  intro i
  try simp only [Vector.getElem_set]
  finite_cases i <;> rfl))

theorem dispatchCoordinates {code : CodeMap} (args : Values Value Reg.count) (mem : Ram) :
    let ax := args[0].get 64
    let cx := (ax.setWidth 32).setWidth 64
    let tag := ax.setWidth 8 &&& 6
    let compressed := tag == 2
    let next := ((args.set 1 ⟨64, mergeGPR 8 tag cx⟩).set 14 ⟨64, args[2].get 64 + 1⟩).set 19
      (.ofBool compressed)
    program.runBlock (dialect code) ⟨.l1214a0, args, mem⟩ =
      if compressed then .jump ⟨.l1214ae, next, mem⟩ else .jump ⟨.l1214b5, next, mem⟩ := by
  dsimp only
  cfg_eval
  simp only [cmpSpec_ZF, setWidth_mergeGPR8]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  by_cases h : (args[0].get 64).setWidth 8 &&& 6 = 2
  · simp only [beq_iff_eq.mpr h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    dispatch_regs
  · simp only [beq_eq_false_iff_ne.mpr h, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    dispatch_regs


theorem dispatchCompact {code : CodeMap} (args : Values Value Reg.count) (mem : Ram) :
    let tag := (args[0].get 64).setWidth 8
    let compact := tag == 5
    program.runBlock (dialect code) ⟨.l1214b5, args, mem⟩ =
      .jump ⟨if compact then .l1214b9 else .l1214f3, args.set 19 (.ofBool compact), mem⟩ := by
  dsimp only
  cfg_eval
  rw [cmpSpec_ZF]
  generalize ((args[0].get 64).setWidth 8 == 5) = compact
  cases compact <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    dispatch_regs

theorem compactParity {code : CodeMap} (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l1214b9, args, mem⟩ =
      .jump ⟨.l1214bb, args.set 7 ⟨64, 0⟩, mem⟩ := by
  cfg_eval
  dispatch_regs

theorem resumeCompressed {code : CodeMap} (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l1214ce, args, mem⟩ = .jump ⟨.l121502, args, mem⟩ := by
  cfg_eval
  dispatch_regs

theorem compressedParity {code : CodeMap} (args : Values Value Reg.count) (mem : Ram) :
    let ax := args[0].get 64
    let parity := ax.setWidth 8 &&& 1
    program.runBlock (dialect code) ⟨.l1214ae, args, mem⟩ =
      .jump ⟨.l1214bb, (args.set 0 ⟨64, mergeGPR 8 parity ax⟩).set 7 ⟨64, parity.setWidth 64⟩, mem⟩ := by
  dsimp only
  cfg_eval
  simp only [setWidth_mergeGPR8]
  dispatch_regs

theorem dispatchIdentity {code : CodeMap} (args : Values Value Reg.count) (mem : Ram)
    (tag : (args[1].get 64).setWidth 32 = 0) :
    program.runBlock (dialect code) ⟨.l1214d0, args, mem⟩ =
      .jump ⟨.l1214d8, args.set 19 (.ofBool true), mem⟩ := by
  cfg_eval
  rw [tag]
  change Transfer.jump _ = _
  dispatch_regs

end K256.Proofs.Sec1.Affine
