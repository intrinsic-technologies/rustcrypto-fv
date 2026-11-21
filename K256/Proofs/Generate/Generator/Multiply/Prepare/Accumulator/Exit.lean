import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem exit {fr : Activation} {a initial : Registers} {m : Ram} {d : Nat}
    (entry : CoreEntry fr initial d) (s : State .l11d719 fr a m) (zero : a[5].get 64 = 0)
    (limit : memLoad m (sp fr + 0x38) 64 = 66) :
    ∃ b, Reaches .l11d719 a m .l11d748 b m ∧ State .l11d748 fr b m := by
  obtain ⟨rsp,_,stack⟩ := currentStack s rfl
  have read : Readable m (sp fr + 0x38) 8 := by apply stack.readable.sub <;> acc_bounds using entry
  have ok := LoadOk.of_region read (Nat.le_refl _) (Nat.le_refl _)
  have top := congrArg (Value.get 64) rsp
  change a[4].get 64 = sp fr at top
  refine ⟨?b, ?reach, ?state⟩
  case reach =>
    have first : program.runBlock (dialect Extracted.programImage) ⟨.l11d719,a,m⟩ =
        .jump ⟨.l11d72f,?c,m⟩ := by
      arithmetic_segment using code_l11d719 [top,zero,limit,ok]
    have second : program.runBlock (dialect Extracted.programImage) ⟨.l11d72f,?c,m⟩ =
        .jump ⟨.l11d748,?b,m⟩ := by arithmetic_segment using code_l11d72f []
    refine Star.step (b := ⟨⟨.l11d72f,?c,m⟩,[]⟩) ?_ (Semantics.Reaches.single ?_)
    all_goals change program.step _ _ = _
    all_goals simp only [Program.step,first,second,Transfer.next]
  case state =>
    apply transported (t := .l11d748) entry s rfl rfl (RamWriteFrame.refl _ _)
    · rintro ⟨i,h⟩ hi
      have w := s.widths ⟨i,h⟩ hi
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w
    · rintro ⟨i,h⟩ hi
      have w := s.savedWidths ⟨i,h⟩ hi
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w
    · rintro ⟨i,h⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
