import K256.Proofs.Ecdh.Multiply.Bases.Compare
import K256.Proofs.Ecdh.Multiply.Bases.Start
import K256.Proofs.Ecdh.Multiply.Bases.Negate
import K256.Proofs.Ecdh.Multiply.Bases.Finish

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Prepare

set_option linter.unusedVariables false in
theorem peerPrepareBases {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (pos : 0 < d) (bound : d < domain.n)
    (s : SplitState fr a m d) :
    ∃ b n, Reaches .l11c9e7 a m .l11cf0d b n ∧ PeerBasesReady fr b n d peer := by
  obtain ⟨_, _, hs, s₁⟩ := Bases.peerStart entry s
  obtain ⟨_, _, hc, s₂⟩ := Bases.peerCompare entry s₁
  obtain ⟨_, _, hn, s₃⟩ := Bases.peerNegate entry s₂
  obtain ⟨b, n, hf, ready⟩ := Bases.peerFinish entry s₃
  exact ⟨b, n, ((hs.trans hc).trans hn).trans hf, ready⟩

end Prepare

end K256.Proofs.Generate.Generator.Multiply
