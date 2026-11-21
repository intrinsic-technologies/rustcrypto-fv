import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Finish.Return

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1

private theorem finalLocals {fr : Activation} {a : Registers} {m : Ram}
    (s : Context fr a m) :
    State .l11cf0d fr a m ∧
    Locals fr m [(0x8,0),(0x60,66),(0x68,152),(0x88,152),(0xc0,0),(0xd8,fr.rcx)] := by
  constructor
  · refine ⟨s.atoms,s.widths,s.savedWidths,coreFrame s.frame,?_⟩
    intro kv hk
    exact s.locals kv (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [localValues])
  · intro kv hk
    exact s.locals kv (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [localValues])

private theorem selectionKeep {fr : Activation} {a b c : Registers} {m q : Ram} {d : Nat}
    (s : Context fr a m) (h : SelectEntry fr a b m q d)
    (rsp : c[4] = ⟨64,sp fr⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) :
    ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → c[i] = a[i] := by
  have ⟨oldRsp, _, _, _, _, _⟩ := s.atoms
  rintro ⟨i,hi⟩ hmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact rsp.trans oldRsp.symm
  all_goals exact (kept _ (by decide +revert)).trans (h.keep _ (by decide +revert))

private theorem selectionContext {fr : Activation} {initial a b c : Registers} {m q n : Ram} {d : Nat}
    (e : CoreEntry fr initial d) (s : Context fr a m) (h : SelectEntry fr a b m q d)
    (frame : RamWriteFrame m n (writes fr selectWrites))
    (rsp : c[4] = ⟨64,sp fr⟩)
    (saved : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → c[i] = ⟨64,b[i].get 64⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (widths : ParseSignature.ArgumentWidths c) : Context fr c n := by
  have savedWidths : SavedWidths c := fun i hi => congrArg Value.width (saved i hi)
  exact s.advance e frame (by decide) (by decide +kernel) widths savedWidths
    (selectionKeep s h rsp kept)

private theorem returnedRegister {v : Word} {b c : Value}
    (after : c = ⟨64,b.get 64⟩) (before : b = ⟨64,v⟩) : c = ⟨64,v⟩ := by
  rw [after,before]
  rfl

private theorem finishReady {fr : Activation} {initial a b c : Registers} {m q n : Ram} {d : Nat}
    (e : CoreEntry fr initial d) (s : Negated fr a m d) (h : SelectEntry fr a b m q d)
    (rsp : c[4] = ⟨64,sp fr⟩)
    (saved : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → c[i] = ⟨64,b[i].get 64⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (widths : ParseSignature.ArgumentWidths c)
    (picked : (if decide (firstComponent d < 0) then generator.neg else generator).Stored n (sp fr + 0x328))
    (foot : RamWriteFrame q n (selectFootprint fr)) : BasesReady fr c n d := by
  have frame := h.frame.trans foot (selectFootprintWithin e)
  obtain ⟨state,extra⟩ := finalLocals (selectionContext e s.toContext h frame rsp saved kept widths)
  have magFirst := WordsAt.of_frame s.firstMagnitude frame (by decide)
    (outside e selectWrites (i := 624) (n := 32) (by decide) (by decide))
  have magSecond := keepSecondMagnitude e h.magnitude foot
  have sign := (frame.memLoad_eq (outside e selectWrites (i := 72) (n := 1) (by decide) (by decide))).trans s.secondSign
  exact ⟨state,⟨magFirst,magSecond⟩,extra,firstBaseFromSelect picked,keepEndo e s.endo frame (by decide),
    sign,returnedRegister (saved 3 (by decide)) h.mask4,
    returnedRegister (saved 12 (by decide)) h.mask52,returnedRegister (saved 14 (by decide)) h.mask48,
    returnedRegister (saved 5 (by decide)) h.basePtr,returnedRegister (saved 15 (by decide)) h.workPtr⟩

theorem finish {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat}
    (e : CoreEntry fr initial d) (s : Negated fr a m d) :
    ∃ b n, Reaches .l11ccfd a m .l11cf0d b n ∧ BasesReady fr b n d := by
  obtain ⟨b,q,entry⟩ := enterSelect e s
  obtain ⟨c,n,reach,rsp,saved,kept,widths,picked,foot⟩ := resumeFirstBase e s entry
  exact ⟨c,n,reach,finishReady e s entry rsp saved kept widths picked foot⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
