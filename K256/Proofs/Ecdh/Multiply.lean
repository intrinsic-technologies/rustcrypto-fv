import K256.Proofs.Ecdh.Multiply.Split
import K256.Proofs.Ecdh.Multiply.Bases
import K256.Proofs.Ecdh.Multiply.Tables
import K256.Proofs.Ecdh.Multiply.Digits
import K256.Proofs.Ecdh.Multiply.Loop

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program K256.Proofs.CFG K256.Proofs.Refine K256.Proofs.Lift
  K256.Proofs.Generate.LIR Standards.SECG.DomainParameters.Secp256k1

theorem peerCoreExecution {fr : Activation} {a : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr a d peer) (pos : 0 < d) (bound : d < domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c880, a, fr.original⟩, []⟩ out ∧
      PeerCoreResult fr d peer out := by
  obtain ⟨_, _, splitPath, split⟩ := peerSplitScalar entry pos bound
  obtain ⟨_, _, basePath, bases⟩ := Prepare.peerPrepareBases entry pos bound split
  obtain ⟨_, _, tablePath, tables⟩ := Prepare.peerPrepareTables (@addCall) entry bases
  obtain ⟨_, _, digitPath, digits⟩ := Prepare.peerPrepareDigits (@Radix.execute) entry pos bound tables
  obtain ⟨_, _, accPath, ready⟩ := Prepare.peerPrepareAccumulator (@lookup) (@addCall) entry pos bound digits
  obtain ⟨out, run, post⟩ := peerWindowLoop (@fourDoubles) (@lookup) (@addCall) entry pos bound ready
  exact ⟨out, Program.Exec.of_sem ((splitPath.trans (basePath.trans (tablePath.trans
    (digitPath.trans accPath)))).exec run.sem), post⟩

end K256.Proofs.Generate.Generator.Multiply
