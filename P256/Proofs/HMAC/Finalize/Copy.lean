import P256.Proofs.SHA256.Interface
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem HashStateAt.copy {s t : RamState} {a b : BitVec 64} {hash : Array UInt32}
    (input : HashStateAt s a hash)
    (bytes : ∀ i < 32, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    HashStateAt t b hash := by
  refine ⟨input.1, fun i hi => ?_⟩
  have eq (j : Nat) (hj : j < 4) :
      t.external[b + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? =
      s.external[a + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? := by
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using bytes (4*i+j) (by omega)
  have h0 := eq 0 (by decide)
  have h1 := eq 1 (by decide)
  have h2 := eq 2 (by decide)
  have h3 := eq 3 (by decide)
  have raw := input.2 i hi
  simp only [loadBytes, loadBytes.loop, addAddress, fromNat, Nat.zero_add, Nat.reduceAdd] at raw ⊢
  rw [h0, h1, h2, h3]
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  simp_all only

end P256.Proofs.SHA256
