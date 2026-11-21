import K256.Proofs.Ecdh.Multiply.Bases.Frame

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Standards.SECG.DomainParameters.Secp256k1

theorem peerOutsidePair {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective} (e : PeerCoreEntry fr initial d peer) :
    Outside [fr.region] fr.rsi 120 := by
  have lo := Split.Caller.peerLowNat e
  have := e.room
  have high := e.high
  rw [e.pairPtr]
  refine ⟨by bv_omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  right; dsimp only [Activation.region]; bv_omega

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
