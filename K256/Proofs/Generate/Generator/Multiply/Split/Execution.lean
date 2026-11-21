import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Execution

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Proofs.Refine Standards.SECG.DomainParameters

theorem splitScalar {fr : Activation} {a : Registers} {d : Nat}
    (entry : CoreEntry fr a d) (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ b m, Reaches .l11c880 a fr.original .l11c9e7 b m ∧ SplitState fr b m d := by
  obtain ⟨b, m, prologue, atoms, count, frame⟩ := Split.prologue entry
  obtain ⟨c, m', reached, split⟩ := Split.calls Split.add Split.mul (Split.round Split.add)
    entry pos bound atoms count frame
  exact ⟨c, m', prologue.trans reached, split⟩

end K256.Proofs.Generate.Generator.Multiply
