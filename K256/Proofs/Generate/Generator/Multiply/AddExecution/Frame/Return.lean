import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.State

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxHeartbeats 800000 in
theorem popReturn {code : CodeMap} {fr : Activation} {b : Values Value 7260} {m : Ram}
    (stack : Writable code m (fr.rsp - 536) 536) (rd : Readable m fr.rsp 8)
    (retLow : fr.ret.toNat < 2^32) (full : AtBody fr b m) (sp : b[7258].get 64 = fr.rsp - 48)
    (cx : b[7247].width = 64) (dx : b[7249].width = 64) (si : b[7251].width = 64)
    (di : b[7243].width = 64) (r8 : b[7151].width = 64) (r9 : b[7159].width = 64) :
    ∃ out, b_l10a410_171.eval (dialect code) b m = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a410.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ out.store = m := by
  obtain ⟨_, _, df, mx, ftw, fcw, _, bx, v12, v13, v14, v15, bp, ret⟩ := full
  refine ⟨?_, ?ev, ?tag, ?done_, ?widths, ?store⟩
  case ev =>
    unfold b_l10a410_171
    simp only [cfg_eval, BitVec.reduceEq, Option.getD_some, and_true, ↓reduceIte,
      sp, Lift.reduceAddOffset, bx, v12, v13, v14, v15, bp, ret, retLow]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10a410)
    rfl
  case tag => rfl
  case done_ => exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  case store => rfl

end K256.Proofs.Generate.Generator.Multiply.AddFrame
