import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Execution

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination

private theorem packFour_value (v : Vector Word 4) : packFour (v.map BitVec.toNat) = value v := by
  simp only [packFour, value, Vector.getElem_map]
  omega

private theorem unpacked {w : Value} (hw : w.width = 64) : Value.mk 64 (w.get 64) = w := by
  cases w with | mk n v => cases hw; simp [Value.get]

theorem linearCombination {a : Registers} {m : Ram} {sp dst ret : Word} {x y : Int} {u v : Word}
    (fr : CalleeFrame a m sp dst ret 112 41)
    (args : LinearArgs a m sp dst 112 41 x y u v) :
    ∃ out, CalleeExec .l1084e0 a m out ∧ CalleeResult a m sp dst ret 112 41 out ∧
      wideSignedAt out.store dst (x * u.toInt + y * v.toInt) := by
  obtain ⟨ls, sl, lw, lsign, lx⟩ := args.left.signed
  obtain ⟨rs, sr, rwds, rsign, ry⟩ := args.right.signed
  let p : Inputs := ⟨ls, rs, signByte sl, signByte sr, u, v⟩
  let initial : LinearCombination.At1084e0 a sp dst ret (a[6].get 64) (a[2].get 64) p a m := {
    toControls := ⟨rfl, rfl, rfl, rfl⟩
    r1 := args.coeffLeft
    r2 := rfl
    r3 := rfl
    r4 := by rw [fr.rsp, Value.get_mk]
    r5 := rfl
    r6 := rfl
    r7 := by rw [fr.rdi, Value.get_mk]
    r8 := args.coeffRight
    r12 := rfl
    r13 := rfl
    r14 := rfl
    r15 := rfl
    mleft0_64 := by simpa [wordAddr, p] using lw 0 (by decide)
    mleft8_64 := by simpa [wordAddr, p] using lw 1 (by decide)
    mleft16_64 := by simpa [wordAddr, p] using lw 2 (by decide)
    mleft24_64 := by simpa [wordAddr, p] using lw 3 (by decide)
    mright0_64 := by simpa [wordAddr, p] using rwds 0 (by decide)
    mright8_64 := by simpa [wordAddr, p] using rwds 1 (by decide)
    mright16_64 := by simpa [wordAddr, p] using rwds 2 (by decide)
    mleft32_8 := lsign
    mright24_64 := by simpa [wordAddr, p] using rwds 3 (by decide)
    mright32_8 := rsign
    msp0_64 := fr.retAddr }
  obtain ⟨out, run, frame, h⟩ := LinearCombination.machine a m sp dst ret _ _ p fr args.left args.right initial
  refine ⟨out, run, ⟨h.tag, h.rsp, ?_, ?_, frame⟩, resultWords p, resultNegative p sl sr, ?_, ?_, ?_⟩
  · intro ⟨i, hi⟩ hm hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> apply Eq.trans _ (unpacked hw)
    all_goals first | exact h.rbx | exact h.rbp | exact h.r12 | exact h.r13 | exact h.r14 | exact h.r15
  · intro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> first | exact h.df | exact h.mxcsr | exact h.ftw | exact h.fcw
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> first
      | simpa [wordAddr] using h.mag0
      | exact h.mag1 | exact h.mag2 | exact h.mag3 | exact h.mag4
  · exact h.sign.trans (resultSign_correct p sl sr rfl rfl)
  · have lhs : inputValue p.a sl = x := by rw [lx, inputValue, packFour_value]
    have rhs : inputValue p.b sr = y := by rw [ry, inputValue, packFour_value]
    have he := resultWords_correct p sl sr rfl rfl
    rw [lhs, rhs] at he
    change signedWideValue (resultWords p) (resultNegative p sl sr) = x*u.toInt + y*v.toInt at he
    rw [← he]
    simp only [signedWideValue, wideValue_eq, Int.natCast_add, Int.natCast_mul]
    split <;> omega

end K256.Proofs.Generate.Generator.Affine.Invert.Core
