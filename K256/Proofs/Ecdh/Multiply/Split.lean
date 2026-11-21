import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Execution
import K256.Proofs.Ecdh.Multiply.Split.Execution

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Proofs.Refine Standards.SECG.DomainParameters

theorem peerSplitScalar {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr a d peer) (_pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ b m, Reaches .l11c880 a fr.original .l11c9e7 b m ∧ SplitState fr b m d := by
  obtain ⟨b, m, peerPrologue, atoms, count, frame⟩ := Split.peerPrologue entry
  obtain ⟨c, m', reached, split⟩ := Split.peerCalls Split.add Split.mul (Split.round Split.add)
    entry bound atoms count frame
  exact ⟨c, m', peerPrologue.trans reached, split⟩

end K256.Proofs.Generate.Generator.Multiply
