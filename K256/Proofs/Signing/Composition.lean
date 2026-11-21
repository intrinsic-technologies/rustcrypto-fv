import K256.Proofs.Signing.Composition.Wrapper
import K256.Proofs.Signing.Composition.Prologue
import K256.Proofs.Signing.Composition.Hash
import K256.Proofs.Signing.Composition.Initialize
import K256.Proofs.Signing.Composition.Enter
import K256.Proofs.Signing.Composition.Attempt
import K256.Proofs.Signing.Composition.Return
import K256.Proofs.Signing.LIR

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem loop {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d) :
    NonceLoop LIR.lifted (signCandidate d msg) (signatureOutput s) (AtCandidate s d msg) := by
  constructor
  · rintro st x pair ⟨head,a,m,rfl,atHead,run⟩ ok
    by_cases range : 0 < (candidate st).1 ∧ (candidate st).1 < domain.n
    · have sig : signCandidate d msg (candidate st).1 = some pair := by
        simpa only [attemptResult, Bool.and_eq_true, decide_eq_true_eq, ite_eq_left range] using ok
      obtain ⟨b,n,generated,ready,bytes⟩ := run.inRange atHead range.1 range.2
      have step := attempt call decoded ready range.1 range.2 bytes
      rw [sig] at step
      obtain ⟨c,t,signed,result⟩ := step
      obtain ⟨out,ret,post⟩ := returnSignature call result
      exact ⟨out, Program.Exec.of_sem ((generated.trans signed).exec ret.sem), post⟩
    · simp only [attemptResult, Bool.and_eq_true, decide_eq_true_eq, ite_eq_right range] at ok
      cases ok
  · rintro st x ⟨head,a,m,rfl,atHead,run⟩ failed
    by_cases range : 0 < (candidate st).1 ∧ (candidate st).1 < domain.n
    · have sig : signCandidate d msg (candidate st).1 = none := by
        simpa only [attemptResult, Bool.and_eq_true, decide_eq_true_eq, ite_eq_left range] using failed
      obtain ⟨b,n,generated,ready,bytes⟩ := run.inRange atHead range.1 range.2
      have step := attempt call decoded ready range.1 range.2 bytes
      rw [sig] at step
      obtain ⟨c,t,rejected,next⟩ := step
      obtain ⟨y,front,atNext⟩ := enter call next
      exact ⟨core .l1058d0 b n,y,generated,by change (0x100ab0 : BitVec 64) ≠ 0x1058d0; decide,rejected.trans front,atNext⟩
    · obtain ⟨b,n,c,t,generated,rejected,next⟩ := run.outOfRange atHead range
      exact ⟨fill .l100ac0 b n,fill .l100ab0 c t,generated,by change (0x100ab0 : BitVec 64) ≠ 0x100ac0; decide,rejected,head,c,t,rfl,next,run⟩

theorem execution [bindings : Bindings] {s : RamState} {secret msg : ByteArray} {d : Nat}
    (machine : MachineRamUnitStrideDecodable bindings s)
    (supported : SupportedIntegerMachineState bindings.processor s)
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d) :
    (∀ count r v, Ecdsa.signatureWithin d msg count = some (r,v) →
      ReturnedSignature s (Ecdsa.normalizeS r v)) ∧
    ((∀ count, Ecdsa.signatureWithin d msg count = none) → NeverReturns s) := by
  obtain ⟨a,m,wrap,entry⟩ := wrapper call decoded
  obtain ⟨b,n,init,iv⟩ := prologue call entry
  obtain ⟨c,t,hashed,digest⟩ := hash call iv
  obtain ⟨e,u,initialized,outer⟩ := initializeNonce call decoded digest
  obtain ⟨x,went,head⟩ := enter call outer
  apply execution_of_nonceLoop machine supported call (entry := LIR.Label.l102630) rfl
    (LIR.blocks machine.stringStride _ Common.fnCode_subset_programImage) ?_
    (wrap.trans (init.trans (hashed.trans (initialized.trans went)))) head (loop call decoded)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end K256.Proofs.Signing.Composition
