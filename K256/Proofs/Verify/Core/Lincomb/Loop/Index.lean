import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem signTest {d : Int} (hd : Naf.ValidDigit d) (hn : d ≠ 0) :
    ((BitVec.ofInt 8 d == 0) || (BitVec.ofInt 8 d).msb) = decide (d < 0) := by
  obtain ⟨odd, lo, hi⟩ := hd.resolve_left hn
  obtain ⟨i, rfl⟩ : ∃ i : Fin 16, d = 2 * (i.val : Int) - 15 :=
    ⟨⟨((d+15)/2).toNat, by omega⟩,by simp only; omega⟩
  exact (show ∀ i : Fin 16,
    let d := 2 * (i.val : Int) - 15
    ((BitVec.ofInt 8 d == 0) || (BitVec.ofInt 8 d).msb) = decide (d < 0) by decide +kernel) i

theorem digitSign {a : Registers} {m : Ram} (d : Int) (hd : Naf.ValidDigit d) (hn : d ≠ 0)
    (byte : a[7] = ⟨64,(BitVec.ofInt 8 d).setWidth 64⟩) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1103c0,a,m⟩ =
      (if d < 0 then .jump ⟨.l110400,b,m⟩ else .jump ⟨.l1103c7,b,m⟩) ∧ b[7] = a[7] ∧ b[0] = a[7] ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have bits : a[7].get 64 = (BitVec.ofInt 8 d).setWidth 64 := congrArg (Value.get 64) byte
  let b := (a[7].get 64).setWidth 8
  let f := testFlags (b &&& b)
  have guard : (f.ZF.getD false || f.SF.getD false != f.OF.getD false) = decide (d < 0) := by
    change ((b &&& b == 0) || ((b &&& b).msb != false)) = _
    have byte' : b = BitVec.ofInt 8 d := by dsimp only [b]; rw [bits]; bv_omega
    simpa [byte'] using signTest hd hn
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval
    rw [guard]
    by_cases h : d < 0 <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> rfl
  case post =>
    refine ⟨rfl,?_,?_⟩
    · change Value.mk 64 ((a[7].get 64).setWidth 32 |>.setWidth 64) = a[7]
      rw [bits, byte]
      congr 1
      bv_omega
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl


theorem positiveIndex {a : Registers} {m : Ram} (d : Int) (hd : Naf.ValidDigit d) (sign : 0 < d)
    (byte : a[7] = ⟨64,(BitVec.ofInt 8 d).setWidth 64⟩) (acc : a[0] = a[7]) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l1103c7,a,m⟩ =
      .jump ⟨.l1103d1,b,m⟩ ∧ b[7].get 64 = BitVec.ofNat 64 (d.natAbs / 2) ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have bits : a[7].get 64 = (BitVec.ofInt 8 d).setWidth 64 := congrArg (Value.get 64) byte
  have accBits := (congrArg (Value.get 64) acc).trans bits
  have values : d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 ∨ d = 11 ∨ d = 13 ∨ d = 15 := by
    rcases hd with h | ⟨odd, lo, hi⟩ <;> omega
  refine ⟨?_,?run,?idx,?keep⟩
  case run =>
    cfg_eval
    simp only [bits, accBits]
    refine Eq.trans (ite_eq_right ?_) ?_
    · rcases values with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    · rfl
  case idx =>
    rcases values with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case keep =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem negativeIndex {a : Registers} {m : Ram} (d : Int) (hd : Naf.ValidDigit d) (sign : d < 0)
    (byte : a[7] = ⟨64,(BitVec.ofInt 8 d).setWidth 64⟩) (acc : a[0] = a[7]) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l110400,a,m⟩ =
      .jump ⟨.l110418,b,m⟩ ∧ b[7].get 64 = BitVec.ofNat 64 (d.natAbs / 2) ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have bits : a[7].get 64 = (BitVec.ofInt 8 d).setWidth 64 := congrArg (Value.get 64) byte
  have accBits := (congrArg (Value.get 64) acc).trans bits
  have values : d = -1 ∨ d = -3 ∨ d = -5 ∨ d = -7 ∨ d = -9 ∨ d = -11 ∨ d = -13 ∨ d = -15 := by
    rcases hd with h | ⟨odd, lo, hi⟩ <;> omega
  refine ⟨?_,?run,?idx,?keep⟩
  case run =>
    cfg_eval
    simp only [bits, accBits]
    refine Eq.trans (ite_eq_right ?_) ?_
    · rcases values with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    · rfl
  case idx =>
    rcases values with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case keep =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Loop
