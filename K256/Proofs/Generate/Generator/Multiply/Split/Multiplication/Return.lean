import K256.Proofs.Generate.Generator.Multiply.Split.Contract

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem mulReturn {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn1099c0.frameAt .l109be7 fr))
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109be7, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = m ∧
      Atom.All Extracted.programImage out.values m (Fn1099c0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values := by
  simp only [Fn1099c0.frameAt, Fn1099c0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, di, mx, ftw, fcw, bx, r12, r13, r14, r15, bp, retRead, ret, low,
    win, room, _, _⟩ := atoms
  have sp : a[4].get 64 = fr.rsp - 184 := congrArg (Value.get 64) rsp
  refine ⟨?out, .done ?run, ?tag, ?store, ?regs, ?widths⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [sp, Lift.reduceAddOffset,
      BitVec.sub_add_cancel,
      bx, r12, r13, r14, r15, bp, ret, low, and_true]
    simp (disch := slot_guard using code_l109be7) only [ite_eq_left]
    rfl
  case tag => rfl
  case store => rfl
  case regs => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ ha
    have hw := widths ⟨i, hi⟩ ha
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

end K256.Proofs.Generate.Generator.Multiply.Split
