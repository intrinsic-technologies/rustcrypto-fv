import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.LIR.Fn10e010.Frame
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Endomorphism.Value

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem run {fr : Activation} {a : Registers} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn10e010.frameAt .l10e010 fr))
    (src : Readable m fr.rsi 120) (dst : Writable Extracted.programImage m fr.rdi 120)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rsi.toNat + 120 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ fr.rsi.toNat)
    (words : WordsAt m fr.rsi 64 inputWords) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10e010.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 128, 128⟩,⟨fr.rdi.toNat, 120⟩] ∧
      WordsAt out.store fr.rdi 64 outputWords := by
  simp only [Fn10e010.frameAt, Fn10e010.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, win, room, align, _⟩ := entry
  have sl := retRead.low
  have xl := src.low
  have dl := dst.readable.low
  have depth : 128 ≤ fr.rsp.toNat := by omega
  have v4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have v3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have v5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have v6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have v7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have v12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have v13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have v14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have v15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have x0 : memLoad m fr.rsi 64 = 0x2815b16f81798 := by
    rw [← BitVec.add_zero fr.rsi]
    exact words 0 (by decide)
  have x1 : memLoad m (fr.rsi + 8) 64 = 0xdb2dce28d959f := words 1 (by decide)
  have x2 : memLoad m (fr.rsi + 16) 64 = 0xe870b07029bfc := words 2 (by decide)
  have x3 : memLoad m (fr.rsi + 24) 64 = 0xbbac55a06295c := words 3 (by decide)
  have x4 : memLoad m (fr.rsi + 32) 64 = 0x79be667ef9dc := words 4 (by decide)
  have x5 : memLoad m (fr.rsi + 40) 64 = 0x7d08ffb10d4b8 := words 5 (by decide)
  have x6 : memLoad m (fr.rsi + 48) 64 = 0x48a68554199c4 := words 6 (by decide)
  have x7 : memLoad m (fr.rsi + 56) 64 = 0xe1108a8fd17b4 := words 7 (by decide)
  have x8 : memLoad m (fr.rsi + 64) 64 = 0xc4655da4fbfc0 := words 8 (by decide)
  have x9 : memLoad m (fr.rsi + 72) 64 = 0x483ada7726a3 := words 9 (by decide)
  have x10 : memLoad m (fr.rsi + 80) 64 = 0x1 := words 10 (by decide)
  have x11 : memLoad m (fr.rsi + 88) 64 = 0x0 := words 11 (by decide)
  have x12 : memLoad m (fr.rsi + 96) 64 = 0x0 := words 12 (by decide)
  have x13 : memLoad m (fr.rsi + 104) 64 = 0x0 := words 13 (by decide)
  have x14 : memLoad m (fr.rsi + 112) 64 = 0x0 := words 14 (by decide)
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?widths, ?frame, ?words⟩
  case run =>
    unfold Program.step
    generate_block [v3, v4, v5, v6, v7, v12, v13, v14, v15, BitVec.add_zero,
      Lift.reduceSubOffset, Lift.reduceAddOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
    segment_words [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
      ret, retLow, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10e010)
    rfl
  case tag => rfl
  case done_ =>
    exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    dsimp only
    repeat' refine RamWriteFrame.memStore ?_ _ ?_
    exact RamWriteFrame.refl _ _
    all_goals simp only [InRegions, InRegion, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left] <;> bv_omega
  case words =>
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      segment_words []
      try rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
