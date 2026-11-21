import K256.Proofs.ParseSignature.Fill.Iteration
import K256.Proofs.ParseSignature.Fill.Setup

namespace K256.Proofs.ParseSignature

open K256.Spec K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR Fill

private theorem savedOutsideLoop {code : CodeMap} {fr : Activation} (pre : MemoryPre code fr)
    (off : BitVec 64) (hOff : off ∈ ([48, 40, 32, 24, 16, 8, 0] : List (BitVec 64))) :
    Outside (loopWrites fr) (fr.rsp - off) 8 := by
  have small : off.toNat ≤ 48 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    rcases hOff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have haddr := pre.stackNat (d := off.toNat) (by omega)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at haddr
  have room := pre.stackRoom
  have low := pre.retReadable.low
  refine ⟨by rw [haddr]; omega, ?_⟩
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right
    have sp80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := pre.stackNat (by decide : 80 ≤ 208)
    simp only [loopStack, buffer, sp80, haddr]
    omega
  · have sep := pre.outputStack.2 (callStack fr) (List.mem_cons_self ..)
    change fr.rdx.toNat + 32 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdx.toNat at sep
    simp only [buffer, haddr]
    omega

theorem fill_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (hn : fr.rsi = 32) (hk : fr.rcx = 4) (hwid : fr.r8 = 256)
    (hr : Readable fr.original fr.rdi 32) (hw : Writable code fr.original fr.rdx 32)
    (hin : Outside [callStack fr] fr.rdi 32) (hout : Outside [callStack fr] fr.rdx 32)
    (hdisj : Outside [buffer fr.rdx 32] fr.rdi 32)
    (hslot : Outside [buffer fr.rdx 32] 0x203dd0 8) :
    Call code .l127d70 LIR.Fn127d70.frameInfo fr [buffer fr.rdx 32] fun out =>
      out.values[0].get 8 = 255 ∧ scalarLimbsAt out.store fr.rdx fr.original fr.rdi := by
  intro args hEntry
  have hmem := hEntry
  change Atom.All code args fr.original (Fn127d70.frameAt .l127d70 fr) at hmem
  simp only [Fn127d70.frameAt, Fn127d70.frameAtG0, Atom.All, Atom.Holds] at hmem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    retReadable, _, retLow, stackWritable, stackRoom, stackAlign, gotReadable, gotValue,
    _, _, _, _, gotStack, _⟩ := hmem
  let memPre : MemoryPre code fr :=
    ⟨hr, hw, retReadable, stackWritable, stackRoom, stackAlign, gotReadable, gotValue,
      gotStack, hslot, hin, hdisj, hout⟩
  obtain ⟨entry, initial, setupRun, setupFrame, saved, width, stack, limit, inputEnd,
    remaining, destination, written, df, mxcsr, ftw, fcw, r8width, r9width⟩ :=
    setupFill hcode fr args hEntry hn hk hwid memPre
  have regs : LoopRegisters fr 0 entry :=
    ⟨width, stack, limit, inputEnd, remaining, destination, written, df, mxcsr, ftw, fcw, r8width, r9width⟩
  have run (i : Nat) (hi : i ≤ 4) : ∃ a m,
      (program.sem (dialect code)).Reaches (loopState 0 entry initial) (loopState i a m) ∧
        LoopRegisters fr i a ∧ (0 < i → ArgumentWidths a) ∧
        RamWriteFrame initial m (loopWrites fr) ∧ filledLimbs fr m i := by
    induction i with
    | zero =>
      refine ⟨entry, initial, .refl _, regs, ?_, RamWriteFrame.refl _ _, ?_⟩
      · intro h
        omega
      · intro j hj
        omega
    | succ i ih =>
      obtain ⟨a, m, prev, loopRegs, _, frame, words⟩ := ih (by omega)
      have global := setupFrame.trans frame (loopWithinWindow fr)
      obtain ⟨a', m', step, loopRegs', widths', frame', words'⟩ :=
        fillIteration hcode memPre (by omega : i < 4) loopRegs global words
      have nextFrame := frame.trans frame' fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
      exact ⟨a', m', prev.trans step, loopRegs', fun _ => widths', nextFrame, words'⟩
  obtain ⟨a, m, loopRun, finalRegs, finalWidths, loopFrame, limbs⟩ := run 4 (by decide)
  have hSaved := saved.of_frame loopFrame (savedOutsideLoop memPre)
  obtain ⟨out, retRun, storeEq, tag, done, widths, status⟩ :=
    fill_return (code := code) fr a m finalRegs.width finalRegs.stack (finalWidths (by decide))
      finalRegs.df finalRegs.mxcsr finalRegs.ftw finalRegs.fcw hSaved retLow
  have reaches := setupRun.trans loopRun
  have hexec := Program.Exec.of_sem (reaches.exec retRun.sem)
  have memory := setupFrame.trans loopFrame (loopWithinWindow fr)
  have framed := (RamWriteFrame.refl _ _).trans memory memPre.writesWithin
  refine ⟨out, hexec, tag, done, ?_, widths, status, ?_⟩
  · rwa [storeEq]
  · rw [storeEq]
    exact limbs

end K256.Proofs.ParseSignature
