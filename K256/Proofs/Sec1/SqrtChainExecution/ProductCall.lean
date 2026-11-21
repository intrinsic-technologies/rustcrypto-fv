import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Square
import K256.Proofs.Sec1.Wrapper.Entry

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

abbrev callerArgs (child : LIR.lifted.Location) (base : Word) : Values Value Reg.count :=
  (show Values Value Reg.count from child.arguments).set 4 ⟨64, base⟩

structure ProductCall (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 13)
    (child : LIR.lifted.Location) (ret : Word) : Prop where
  entry : Sqrt.LiftedSquare.Entry code child (fr.rsp - 440) ret (words a (2 * (i.val + 1)))
  frame : Atom.All code (callerArgs child (fr.rsp - 440)) child.store
    (LIR.Fn115950.frameAt squarePC[i] fr)
  saved : Atom.All code child.arguments child.store (savedAtoms i.succ (fr.rsp - 440) a)
  src : i.val ≠ 0 → child.arguments[(srcReg i).val].get 64 = fr.rsp - 440
  dst : i.val ≠ 0 → child.arguments[(dstReg i).val].get 64 = fr.rsp - 440 + 40
  source : WordsAt child.store fr.rsi 64 a
  sourceRead : Readable child.store fr.rsi 40
  destWrite : Writable code child.store fr.rdi 41
  writes : RamWriteFrame fr.original child.store [fr.region, ⟨fr.rdi.toNat, 41⟩]

end K256.Proofs.Sec1.SqrtChainExecution
