import K256.Proofs.Signing.Composition.Attempt.Decode
import K256.Proofs.Signing.Composition.Attempt.Inverse
import K256.Proofs.Signing.Composition.Attempt.Coordinates
import K256.Proofs.Signing.Composition.Attempt.Arithmetic
import K256.Proofs.Signing.Composition.Attempt.Return
import K256.Proofs.Signing.Scalar.Signature

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Verify.Core (Registers)

theorem attempt {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d)
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (outer : Outer s d msg st a m) (pos : 0 < k) (bound : k < domain.n)
    (nonce : (⟨(sp s+384).toNat,32⟩ : MemoryRegion).HasBytes m (Encoding.natToOctets 32 k)) :
    match signCandidate d msg k with
    | none => ∃ b n, Reach (core .l1058d0 a m) (core .l105886 b n) ∧ Outer s d msg st b n
    | some pair => ∃ b n, Reach (core .l1058d0 a m) ⟨⟨.l102795,b,n⟩,[]⟩ ∧ Result s pair b n := by
  have secretRange : 0 < d ∧ d < domain.n := by
    dsimp only [Keys.decodeSecret] at decoded
    split at decoded
    next valid =>
      have eq := Option.some.inj decoded
      subst d
      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
      exact ⟨valid.1.2,valid.2⟩
    next => contradiction
  obtain ⟨b,n,parseRun,parsed⟩ := Attempt.decode call outer pos bound nonce
  obtain ⟨c,o,inverseRun,scalars⟩ := Attempt.invertAndReduceDigest call parsed pos bound
  obtain ⟨e,p,x,y,pointRun,coords⟩ := Attempt.coordinates call scalars pos bound
  obtain ⟨f,q,arithmeticRun,words⟩ := Attempt.arithmetic call coords secretRange.2
  let r := Nat.mod x domain.n
  let sigS := Attempt.signatureScalar d msg k r
  have digestSize : (SHA256.hashBytes msg).size = 32 := Vector.size_toArray _
  have npos : 0 < domain.n := Nat.zero_lt_of_lt bound
  have finished := Attempt.finish call words (Nat.mod_lt _ npos) (Nat.mod_lt _ npos)
  have outcome : signCandidate d msg k = if r = 0 ∨ sigS = 0 then none else some (r,sigS) :=
    Scalar.signWithNonce_of_coordinates secretRange ⟨pos,bound⟩ coords.point digestSize
  have candidatePath := parseRun.trans (inverseRun.trans (pointRun.trans arithmeticRun))
  by_cases zero : r = 0 ∨ sigS = 0
  · rw [outcome, ite_eq_left zero]
    rw [ite_eq_left zero] at finished
    obtain ⟨g,t,tail,next⟩ := finished
    exact ⟨g,t,candidatePath.trans tail,next⟩
  · rw [outcome, ite_eq_right zero]
    rw [ite_eq_right zero] at finished
    obtain ⟨g,t,tail,result⟩ := finished
    exact ⟨g,t,candidatePath.trans tail,result⟩

end K256.Proofs.Signing.Composition
