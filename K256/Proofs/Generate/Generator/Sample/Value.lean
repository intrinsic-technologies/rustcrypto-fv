import K256.Proofs.Generate.Generator.Sample.State

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem word_eq_limb {s : RamState} {random : ByteArray} {i d : Nat}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (bound : i < random.size / 32)
    (accepted : Sampling.decodeBlock random i = some d) (j : Nat) (hj : j < 4) :
    word s i j = BitVec.ofNat 64 (d / 2^(64*j)) := by
  have input : ValidInput s (registerRegion s .rsi random.size) random := call.inputsInMemory.1
  have h := Sampling.decodeBlock_eq input.2.2 bound
  change Sampling.decodeBlock random i = if _ then some (Sampling.limbsValue (word s i 0)
    (word s i 1) (word s i 2) (word s i 3)) else none at h
  rw [accepted] at h
  split at h <;> cases h
  apply BitVec.eq_of_toNat_eq
  have h0 := (word s i 0).isLt
  have h1 := (word s i 1).isLt
  have h2 := (word s i 2).isLt
  have h3 := (word s i 3).isLt
  rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega with rfl | rfl | rfl | rfl <;>
    simp only [Sampling.limbsValue, BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow] <;> omega

end K256.Proofs.Generate.Generator.Sample
