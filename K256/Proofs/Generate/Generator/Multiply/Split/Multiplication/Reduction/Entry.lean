import K256.Proofs.Generate.LIR.Fn11b510.Frame
import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxHeartbeats 800000 in
theorem reduceEntry {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn11b510.frameAt .l11b510 fr))
    (zero : fr.rdx = 0) :
    ∃ b m', Reaches .l11b510 a m .l11b5a3 b m' ∧
      Atom.All Extracted.programImage b m' (Fn11b510.frameAt .l11b5a3 fr) ∧
      b[7] = ⟨64, 0xbaaedce6af48a03b⟩ ∧ b[9] = ⟨64, 0x402da1732fc9bebf⟩ ∧
      RamWriteFrame m m' [⟨fr.rsp.toNat - 0x81, 0x81⟩] := by
  simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, stack, low, align, _⟩ := atoms
  have get (i : Fin Reg.count) (v : BitVec 64) (h : a[i.val] = ⟨64, v⟩) :
      a[i.val].get 64 = v := by rw [h]; rfl
  have g4 : a[4].get 64 = fr.rsp := get 4 _ sp
  have g2 : a[2].get 64 = fr.rdx := get 2 _ dx
  have g3 : a[3].get 64 = fr.rbx := get 3 _ bx
  have g5 : a[5].get 64 = fr.rbp := get 5 _ bp
  have g7 : a[7].get 64 = fr.rdi := get 7 _ di
  have g12 : a[12].get 64 = fr.r12 := get 12 _ r12
  have g13 : a[13].get 64 = fr.r13 := get 13 _ r13
  have g14 : a[14].get 64 = fr.r14 := get 14 _ r14
  have g15 : a[15].get 64 = fr.r15 := get 15 _ r15

  have depth : 0x81 ≤ fr.rsp.toNat := by omega
  have limit := retRead.low
  refine ⟨?b, ?m, ?reach, ?atoms, ?reg7, ?reg9, ?frame⟩
  case reach =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11b510, a, m⟩ =
        .jump ⟨.l11b5a3, ?b, ?m⟩ := by
      arithmetic_segment using code_l11b510 [g4, g2, g3, g5, g7, g12, g13, g14, g15, zero,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
        BitVec.reduceAdd, BitVec.reduceSub]
    refine .step (b := ⟨⟨.l11b5a3, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next]
  case reg7 | reg9 => rfl
  case atoms =>
    simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds]
    refine ⟨rfl, df, cx, dx, bx, bp, si, r8, r12, r13, r14, r15, mx, ftw, fcw,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?read, ?_, retLow, ?win, low, align, trivial⟩
    case' read | win => slot_state region
    all_goals refine_norm [ret]
  case frame => slot_state region

set_option maxHeartbeats 800000 in
theorem reduceConstants {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn11b510.frameAt .l11b5a3 fr))
    (const1 : a[7] = ⟨64, 0xbaaedce6af48a03b⟩) (const0 : a[9] = ⟨64, 0x402da1732fc9bebf⟩) :
    ∃ b m', Reaches .l11b5a3 a m .l11b5ba b m' ∧
      Atom.All Extracted.programImage b m' (Fn11b510.frameAt .l11b5ba fr) ∧
      b[9] = ⟨64, 0x402da1732fc9bebf⟩ ∧
      memLoad m' (fr.rsp - 0x48) 64 = 0xfffffffffffffffe ∧
      memLoad m' (fr.rsp - 0x60) 64 = 0xffffffffffffffff ∧
      memLoad m' (fr.rsp - 0x50) 64 = 0xbaaedce6af48a03b ∧
      RamWriteFrame m m' [⟨fr.rsp.toNat - 0x81, 0x81⟩] := by
  simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, cx, dx, bx, bp, si, r8, r12, r13, r14, r15, mx, ftw, fcw,
    di, bxSlot, r12Slot, r13Slot, r14Slot, r15Slot, bpSlot, retRead, ret, retLow, win,
    room, align, _⟩ := atoms
  have g4 : a[4].get 64 = fr.rsp - 0x78 := congrArg (Value.get 64) sp
  have g7 : a[7].get 64 = 0xbaaedce6af48a03b := congrArg (Value.get 64) const1
  have depth : 0x81 ≤ fr.rsp.toNat := by omega
  have limit := retRead.low
  refine ⟨?b, ?m, ?reach, ?atoms, ?r9, ?s48, ?s60, ?s50, ?frame⟩
  case reach =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11b5a3, a, m⟩ =
        .jump ⟨.l11b5ba, ?b, ?m⟩ := by
      arithmetic_segment using code_l11b5a3 [g4, g7,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
        BitVec.reduceAdd, BitVec.reduceSub]
    refine .step (b := ⟨⟨.l11b5ba, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next]
  case atoms =>
    simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds]
    refine ⟨sp, df, bx, bp, si, r8, r12, r13, r14, r15, mx, ftw, fcw,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?read, ?_, retLow, ?win, room, align, trivial⟩
    case' read | win => slot_state region
    all_goals refine_norm [di, bxSlot, r12Slot, r13Slot, r14Slot, r15Slot, bpSlot, ret]
  case r9 => exact const0
  case s48 | s60 | s50 => refine_norm []
  case frame => slot_state region

end K256.Proofs.Generate.Generator.Multiply.Split
