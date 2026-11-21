import K256.Proofs.Verify.Core.Lincomb.PeerPath.Copy
import K256.Proofs.Verify.Core.Lincomb.PeerPath.Fill
import K256.Proofs.Verify.Core.Lincomb.PeerPath.Prepare

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

theorem peerPath (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hv : v < domain.n) {d n}
    (saved : CallerFrame fr c d m n) (generator : GeneratorPrepared fr d n u) :
    ∃ f t, Reaches .l10fba8 d n .l10fc13 f t ∧ CallerFrame fr c f m t ∧ PeerPrepared fr f t p u v := by
  obtain ⟨x, m₁, copies, frame₁, gen₁, regs₁⟩ := copyGenerator e h args saved generator
  obtain ⟨y, m₂, fills, frame₂, gen₂, regs₂, zero⟩ := fillPeerDigits e h args frame₁ gen₁ regs₁
  obtain ⟨f, t, prep, frame₃, peer⟩ := preparePeer e h args hv frame₂ gen₂ regs₂ zero
  exact ⟨f, t, (copies.trans fills).trans prep, frame₃, peer⟩

end K256.Proofs.Verify.Core.Lincomb
