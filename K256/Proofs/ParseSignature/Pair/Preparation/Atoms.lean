import K256.Proofs.ParseSignature.Pair.Preparation.Memory

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

variable {fr : Activation} {code : CodeMap} {m : Ram} {regs : Values Value Reg.count}

theorem childAtoms {ret : BitVec 64}
    (caller : Atom.All code (regs.set 4 ⟨64, sp fr⟩) m (Fn103ac0.frameAt .l103b07 fr))
    (widths : ArgumentWidths regs) (rsp : regs[4] = ⟨64, fr.rsp - 192⟩)
    (rdi : regs[7] = ⟨64, sp fr + 8⟩) (rsi : regs[6] = ⟨64, sp fr + 72⟩)
    (rdx : regs[2] = ⟨64, 32⟩) (returnWord : memLoad m (fr.rsp - 192) 64 = ret)
    (small : ret.toNat < 2 ^ 32) :
    Atom.All code regs m (Fn107730.frameInfo.entryAtoms (scalarChild fr ret regs m)) := by
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds, Fin.getElem_fin, Vector.getElem_set] at caller
  obtain ⟨_, df, bx, bp, r12, r13, r14, r15, mxcsr, ftw, fcw, _, _, _, _, _, win, room,
    aligned, s1, v1, s2, v2, s3, v3, apart, _⟩ := caller
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  have low : (fr.rsp - 560).toNat = fr.rsp.toNat - 560 := stackSub_toNat room 560 (by decide)
  have child : (fr.rsp - 192).toNat = fr.rsp.toNat - 192 := stackSub_toNat room 192 (by decide)
  have readRet := (stackWordWritable win 192 (by decide) (by decide)).readable
  have window : Writable code m (fr.rsp - 192 - 368) 368 := by
    rw [BitVec.sub_sub]
    exact win.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  change Atom.All code regs m (Fn107730.frameAt .l107730 (scalarChild fr ret regs m))
  simp only [Fn107730.frameAt, Fn107730.frameAtG0, Atom.All, Atom.Holds]
  refine ⟨rsp, df, entryArgument widths fr 1 (by decide), rdx, bx, bp, rsi, rdi,
    entryArgument widths fr 8 (by decide), entryArgument widths fr 9 (by decide), r12, r13,
    r14, r15, mxcsr, ftw, fcw, readRet, returnWord, small, window, ?_, ?_,
    s1, v1, s2, v2, s3, v3, ?_, trivial⟩ <;>
    omega

theorem scalarEntry_of_copy (src ret : BitVec 64) (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (frame : RamWriteFrame fr.original m [fr.region])
    (caller : Atom.All code (regs.set 4 ⟨64, sp fr⟩) (putScalar fr m src ret)
      (Fn103ac0.frameAt .l103b07 fr))
    (widths : ArgumentWidths regs) (rsp : regs[4] = ⟨64, fr.rsp - 192⟩)
    (rdi : regs[7] = ⟨64, sp fr + 8⟩) (rsi : regs[6] = ⟨64, sp fr + 72⟩)
    (rdx : regs[2] = ⟨64, 32⟩) (small : ret.toNat < 2 ^ 32) :
    ScalarEntry code fr ret src regs (putScalar fr m src ret) := by
  have returnWord : memLoad (putScalar fr m src ret) (fr.rsp - 192) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  exact ⟨childAtoms caller widths rsp rdi rsi rdx returnWord small, ⟨_, caller⟩,
    frame.trans (putScalar_top room (.refl m _) src ret) (topWritesWithin room),
    putScalar_words fr m src ret⟩

abbrev callerLayout (fr : Activation) := Fn103ac0.frameAt .l103b07 fr

theorem callerAtoms {old : Ram} {oldArgs : Values Value Reg.count}
    (tail : Atom.All code oldArgs old ((callerLayout fr).drop 13))
    (registers : Atom.All code regs m ((callerLayout fr).take 11))
    (bx : memLoad m (fr.rsp - 16) 64 = fr.rbx) (r14 : memLoad m (fr.rsp - 8) 64 = fr.r14)
    (frame : RamWriteFrame old m (topWrites fr)) :
    Atom.All code regs m (callerLayout fr) := by
  change Readable old fr.rsp 8 ∧ _ at tail
  obtain ⟨read, ret, small, win, room, align, s1, v1, s2, v2, s3, v3, apart, _⟩ := tail
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  have top := read.low
  have base : (fr.rsp - 192).toNat = fr.rsp.toNat - 192 := stackSub_toNat room 192 (by decide)
  have got (a : BitVec 64) (lo : 0x203dd0 ≤ a.toNat) (hi : a.toNat + 8 ≤ 0x203e28) :
      Outside (topWrites fr) a 8 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change a.toNat + 8 ≤ (fr.rsp - 192).toNat ∨ (fr.rsp - 192).toNat + 192 ≤ a.toNat
    change 0x204058 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at apart
    omega
  have retOutside : Outside (topWrites fr) fr.rsp 8 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (fr.rsp - 192).toNat + 192 ≤ fr.rsp.toNat; omega)
  obtain ⟨rsp, df, b, bp, a12, a13, a14, a15, mx, ftw, fcw, _⟩ := registers
  exact ⟨rsp, df, b, bp, a12, a13, a14, a15, mx, ftw, fcw, bx, r14,
    read.of_frame frame, (frame.memLoad_eq retOutside).trans ret, small, win.of_frame frame,
    room, align, s1.of_frame frame, (frame.memLoad_eq (got _ (by decide) (by decide))).trans v1,
    s2.of_frame frame, (frame.memLoad_eq (got _ (by decide) (by decide))).trans v2,
    s3.of_frame frame, (frame.memLoad_eq (got _ (by decide) (by decide))).trans v3, apart, trivial⟩

end K256.Proofs.ParseSignature.Pair
