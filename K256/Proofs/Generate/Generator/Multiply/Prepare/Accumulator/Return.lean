import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame
import K256.Proofs.Generate.LIR.Fn10a410.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem returned {fr : Activation} {a b : Registers} {m : Ram} {l t r : Label}
    {tag : BitVec 64} {out : Output Value Ram Reg.count} (s : State l fr a m)
    (layout : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr l t r tag a b m)
    (done_ : Atom.All Extracted.programImage out.values out.store
      (Fn10a410.doneAt (child fr b (memStore m (sp fr - 8) tag) tag))) :
    out.values[4] = ⟨64,sp fr⟩ ∧
    ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → out.values[i] = b[i] := by
  have h := s.atoms
  rw [layout] at h
  obtain ⟨_,df,mx,ft,fc,_⟩ := h
  obtain ⟨rsp,keep⟩ := Sample.sampleChildReturn (base := childBase fr b) done_
  refine ⟨by simpa only [childBase,BitVec.sub_add_cancel] using rsp,?_⟩
  have gp (v : Value) (w : v.width = 64) : Value.mk 64 (v.get 64) = v := by
    cases v with | mk n bits => cases w; rfl
  intro ⟨i,hi⟩ hm
  have val := keep ⟨i,hi⟩ hm
  simp only [Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact val.trans (gp b[3] (c.saved 3 (by decide)))
    | exact val.trans (gp b[5] (c.saved 5 (by decide)))
    | exact val.trans (gp b[12] (c.saved 12 (by decide)))
    | exact val.trans (gp b[13] (c.saved 13 (by decide)))
    | exact val.trans (gp b[14] (c.saved 14 (by decide)))
    | exact val.trans (gp b[15] (c.saved 15 (by decide)))
    | exact val.trans ((c.control 22 (by decide)).trans df).symm
    | exact val.trans ((c.control 39 (by decide)).trans mx).symm
    | exact val.trans ((c.control 50 (by decide)).trans ft).symm
    | exact val.trans ((c.control 51 (by decide)).trans fc).symm

theorem resumeState {fr : Activation} {initial a b : Registers} {m n : Ram} {d : Nat}
    {l t r : Label} {tag : BitVec 64} {regs : Registers}
    (entry : CoreEntry fr initial d) (s : State l fr a m)
    (old : Fn11c880.frameAt l fr = Fn11c880.frameAt .l11c9e7 fr)
    (next : Fn11c880.frameAt r fr = Fn11c880.frameAt .l11c9e7 fr)
    (c : WindowCall fr l t r tag a b m)
    (frame : RamWriteFrame m n (writes fr)) (args : ParseSignature.ArgumentWidths regs)
    (rsp : regs[4] = ⟨64,sp fr⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → regs[i] = b[i]) :
    State r fr regs n := by
  apply transported entry s old next frame args
  · intro i hi
    rw [keep i (by simp only [Activation.calleeSavedNumbers,Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact c.saved i hi
  · intro i hi
    rcases List.mem_cons.mp hi with hh|hh
    · obtain rfl : i = 4 := Fin.ext hh
      exact rsp.trans (currentStack s old).1.symm
    · exact (keep i (by simp only [Sample.nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at hh ⊢; omega)).trans (c.control i hh)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
