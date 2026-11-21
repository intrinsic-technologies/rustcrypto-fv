import P256.Proofs.Verifying.Combination.Interface
import P256.Proofs.Projective.Preserve
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem InputAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {p q : Projective} {u v : Nat} (input : InputAt s source p q u v)
    (bytes : ∀ i < 256, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : InputAt t destination p q u v := by
  refine ⟨input.1.of_bytes_eq (fun i hi => bytes i (by omega)), ⟨input.2.1.1, ?_⟩,
    input.2.2.1.of_bytes_eq ?_, ⟨input.2.2.2.1, ?_⟩⟩
  · intro i hi
    have h := bytes (96+i) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h.trans (input.2.1.2 i hi)
  · intro i hi
    have h := bytes (128+i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc] at h
    exact h
  · intro i hi
    have h := bytes (224+i) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h.trans (input.2.2.2.2 i hi)

theorem input_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 96, Stack.region s 8808])
    {i : Nat} (hi : i < 256) :
    t.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply frame_read frame (region := registerRegion s .rsi 256) ?_
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  intro region hr
  have h : region = registerRegion s .rdi 96 ∨ region = Stack.region s 8808 := by simpa using hr
  rcases h with rfl | rfl
  · exact pre.separation 0 1 (by decide)
  · exact pre.separation 0 2 (by decide)

end P256.Proofs.Verifying.Combination
