import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Frame
import ChaCha20Poly1305.Proofs.Decrypt.Segment
import ChaCha20Poly1305.Proofs.Decrypt.Refine
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Part2

namespace ChaCha20Poly1305.Proofs.Decrypt.TagCompare
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

inductive Label | checkTag | take | reject

structure Input where
  computedLo : BitVec 64
  computedHi : BitVec 64
  suppliedLo : BitVec 64
  suppliedHi : BitVec 64

def ok (x : Input) := x.computedLo = x.suppliedLo ∧ x.computedHi = x.suppliedHi

def program (good : Bool) : Program (fun _ => _root_.Empty) Label (fun _ => 0) 0 := ⟨fun
  | .checkTag => .terminate (.br ⟨if good then .take else .reject,#v[]⟩)
  | _ => .terminate (.ret #v[])⟩

@[refine_layout] def layout (x : Input) (good : Bool) : LayoutCore (program good) Empty.semantics lifted Unit where
  start | .checkTag => .l100577 | .take => .l1005d2 | .reject => .l1005ea
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ fr _ := match l with
    | .checkTag => [.mem (fr.rsp - 280) 64 x.computedLo,.mem (fr.rsp - 272) 64 x.computedHi,
      .mem (fr.rsp - 240) 64 x.suppliedLo,.gpr 5 x.suppliedHi,
      .fact (fr.rsp.toNat ≤ 0x100577 ∨ 0x1005d2 + 440 ≤ fr.rsp.toNat)]
    | .take => []
    | .reject => [.low 0 8 1]
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ _ => []
  footprint := fun _ _ => []

set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option pp.maxSteps 160
theorem lowMerge (k : Nat) (h : k ≤ 16) (v : BitVec 16) (old : BitVec 64) :
    (mergeGPR 16 v old).setWidth k = v.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, show (16 : Nat) ≠ 32 by decide, ite_false, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [show i < 16 by omega]

theorem flag {w} (a b : BitVec w) :
    (xorFlags (a ^^^ b)).ZF.getD false = decide (a = b) := by
  change (a ^^^ b == 0#w) = _
  simp only [Bool.beq_eq_decide_eq,BitVec.xor_eq_zero_iff]

theorem block (x : Input) (good : Bool) (hg : ok x ↔ good=true) :
    (Layout.withFrame Fn1001f0.frameAt Fn1001f0.doneAt (layout x good)).BlockSimulation fnCode .checkTag := by
  cases good <;> simp [ok] at hg
  all_goals refine_one [program,layout,setWidth_mergeGPR8]
  all_goals rw [atom8.symm.trans atom25] at hc
  all_goals by_cases hlo : x.computedLo = x.suppliedLo <;> by_cases hhi : x.computedHi = x.suppliedHi
  all_goals try solve | exact False.elim (hg hlo hhi) | exact False.elim (hlo hg.1) | exact False.elim (hhi hg.2)
  all_goals simp only [flag] at hc
  all_goals simp +decide [hlo,hhi,lowMerge,BitVec.setWidth_setWidth_of_le] at hc

end ChaCha20Poly1305.Proofs.Decrypt.TagCompare
