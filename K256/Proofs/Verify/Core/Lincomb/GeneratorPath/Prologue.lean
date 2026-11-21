import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.State
import K256.Proofs.Verify.Core.Lincomb.Phases
import K256.Proofs.Sec1.Serialize.Assemble.Memory

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

private theorem saveGpr {v : Value} {bits : BitVec 64} (h : v = ⟨64, bits⟩) :
    (⟨64, v.get 64⟩ : Value) = v := by rw [h, Value.get_mk]

theorem generatorPrologue (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) :
    ∃ x n, program.runBlock (dialect Extracted.programImage) ⟨.l10fb20, c, push m fr⟩ =
      .call ⟨.l12a700, x, n⟩ ⟨.l10fb7f, #v[], rfl, some ⟨64, 0x10fb7f⟩⟩ ∧
      FillArguments fr x (slot fr 0x228) ∧ PreparesGenerator fr x ∧
      CallerFrame fr c (x.set 4 ⟨64, workSp fr⟩) m n ∧
      memLoad n (workSp fr - 8) 64 = 0x10fb7f := by
  have sp : c[4].get 64 = fr.rsp - 496 := by
    rw [args.sp, Value.get_mk, localSp, BitVec.sub_sub]
    rfl
  have dst := congrArg (Value.get 64) args.dst
  have key := congrArg (Value.get 64) args.peer
  have left := congrArg (Value.get 64) args.u
  have right := congrArg (Value.get 64) args.v
  simp only [Value.get_mk] at dst key left right
  have stack := e.stack.of_frame h.frame
  have bottom := e.low_toNat
  have top := ScalarProduct.belowNat e (off := 488) (by decide)
  change (localSp fr).toNat = _ at top
  have room := e.stackRoom
  have high := e.low
  have writable (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 12456) :
      Writable Extracted.programImage m (fr.rsp - off) 8 := by
    have pos := ScalarProduct.belowNat e hi
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at pos
    exact stack.sub (by omega) (by omega)
  have work : workSp fr = fr.rsp - 10952 := by rw [workSp, localSp, BitVec.sub_sub]; rfl
  have callSp : workSp fr - 8 = fr.rsp - 10960 := by rw [work, BitVec.sub_sub]; rfl
  have digits : slot fr 0x228 = fr.rsp - 10400 := by rw [slot, work]; bv_omega
  have nextDigits : slot fr 0x338 = fr.rsp - 10128 := by rw [slot, work]; bv_omega
  have df : c[22] = ⟨1, 0⟩ := (args.keep 22 (by decide)).trans h.df
  have code : ∀ x ∈ codeRange 0x10fb20 bytes_l10fb20, x ∈ Extracted.programImage :=
    fun x hx => Common.fnCode_subset_programImage x (code_l10fb20 x hx)
  refine ⟨?_, ?_, ?run, ?fill, ?regs, ?frame, ?ret⟩
  case run =>
    cfg_eval [b_l10fb20, b_l10fb20_1, sp, dst, key, left, right,
      Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
    repeat'
      (refine Eq.trans (ite_eq_left ?_) ?_
       apply Sec1.Serialize.Assemble.storeOk_inBlock (included := code)
       · repeat' (with_reducible apply Writable.memStore)
         exact writable _ (by decide) (by decide)
       · decide)
    rfl
  case fill =>
    refine ⟨?_, rfl, rfl, ?_, congrArg (Value.get 1) df⟩
    · rw [callSp]
      rfl
    · exact congrArg (Value.mk 64) digits.symm
  case regs =>
    refine ⟨rfl, ?_, rfl, ?_, rfl, rfl⟩
    · exact congrArg (Value.mk 64) nextDigits.symm
    · exact congrArg (Value.mk 64) digits.symm
  case frame =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [work]
      rfl
    · intro ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> rfl
    · rw [work]
      refine_norm []
    · intro ⟨i, bound⟩
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        refine_norm [slot, work, savedGprs, Nat.reduceAdd, Nat.reduceMul,
          Lift.reduceSubOffset, Lift.reduceAddOffset]
      · exact saveGpr ((args.keep 3 (by decide)).trans h.dst)
      · exact saveGpr ((args.keep 12 (by decide)).trans h.uPtr)
      · exact saveGpr args.result
      · exact saveGpr ((args.keep 14 (by decide)).trans h.key)
      · exact saveGpr ((args.keep 15 (by decide)).trans h.vPtr)
      · exact saveGpr ((args.keep 5 (by decide)).trans h.rbp)
    · refine_norm [slot, work, localSp, push, Lift.reduceSubOffset, Lift.reduceAddOffset]
    · have within (off : Nat) (lo : 496 ≤ off) (hi : off ≤ 12456) :
          InRegions (writes fr) (fr.rsp - BitVec.ofNat 64 off) 8 := by
        have pos := ScalarProduct.belowNat e hi
        exact ⟨_, List.mem_cons_self, by dsimp only [writes, InRegion]; omega⟩
      rw [show localSp fr - 8 = fr.rsp - 496 by unfold localSp; bv_omega]
      repeat' apply RamWriteFrame.memStore _ _ (within _ (by decide) (by decide))
      exact .refl _ _
  case ret =>
    rw [callSp]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Verify.Core.Lincomb
