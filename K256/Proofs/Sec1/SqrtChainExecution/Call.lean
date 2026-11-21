import K256.Proofs.Sec1.SqrtChainExecution.Squares
import K256.Proofs.Sec1.SqrtChainExecution.Execution
import K256.Proofs.Sec1.Sqrt.Finish.CompareStatus
import K256.Proofs.Sec1.Sqrt.FirstStage
import K256.Proofs.Sec1.SqrtProducts.Stage
import K256.Proofs.Sec1.SqrtLaterProducts.Stages

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

theorem productStages {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    (g : Geometry code fr) (ha : FieldRepr a x 8) (i : Fin 13) : MultiplyStage code fr a i := by
  intro args mem state
  if h0 : i = 0 then
    subst i
    exact Sqrt.firstStage g state
  else if h1 : i = 1 then
    subst i
    exact SqrtProducts.secondStage g state
  else
    exact SqrtLaterProducts.laterStages i (by omega) g ha state

theorem execution {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus}
    {args : Values Value Reg.count} (g : Geometry code fr)
    (frame : Atom.All code args fr.original (LIR.Fn115950.frameAt .l115950 fr))
    (input : WordsAt fr.original fr.rsi 64 a) (rd : Readable fr.original fr.rsi 40)
    (wr : Writable code fr.original fr.rdi 41) (ha : FieldRepr a x 8) :
    ∃ o, LIR.program.Exec (dialect code) ⟨⟨.l115950,args,fr.original⟩,[]⟩ o ∧
      FieldRepr (words a 27) (candidate x) 8 ∧
      Return code fr (words a 27) (if candidate x * candidate x = x then 1 else 0) o :=
  executionOfStages g frame input rd wr ha (productStages g ha) (squareStages g)
    (Sqrt.Finish.compareStage g)

end K256.Proofs.Sec1.SqrtChainExecution
