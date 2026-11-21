import K256.Proofs.Sec1.SqrtChainExecution.Composition
import K256.Proofs.Sec1.SqrtChainExecution.Entry

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

theorem executionOfStages {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    {args : Values Value Reg.count} (g : Geometry code fr)
    (frame : Atom.All code args fr.original (LIR.Fn115950.frameAt .l115950 fr))
    (input : WordsAt fr.original fr.rsi 64 a) (rd : Readable fr.original fr.rsi 40)
    (wr : Writable code fr.original fr.rdi 41) (ha : FieldRepr a x 8)
    (mul : ∀ i, MultiplyStage code fr a i) (square : ∀ i, SquareStage code fr a i)
    (finish : CompareStage code fr a) :
    ∃ o, LIR.program.Exec (dialect code) ⟨⟨.l115950,args,fr.original⟩,[]⟩ o ∧
      FieldRepr (words a 27) (candidate x) 8 ∧
      Return code fr (words a 27) (if candidate x * candidate x = x then 1 else 0) o := by
  obtain ⟨b,m,reach,state⟩ := enter g frame input rd wr
  obtain ⟨o,body,repr,post⟩ := finishChain ha state mul square finish
  exact ⟨o,Program.Exec.of_sem (reach.exec body.sem),repr,post⟩

end K256.Proofs.Sec1.SqrtChainExecution
