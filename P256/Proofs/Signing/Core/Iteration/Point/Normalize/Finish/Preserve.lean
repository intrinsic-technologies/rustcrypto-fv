import P256.Proofs.Signing.Core.Iteration.Point.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem region_byte {s t u : RamState} {cs : List Component} {offset len i : Nat}
    (agrees : AgreesExcept cs t u)
    (covers : ∀ c ∈ cs, ∀ a, c.Covers a → (Component.mem (frameBase s+BitVec.ofNat 64 offset) len).Covers a)
    (bound : offset+len < 2^64) (small : i < 2^64) (apart : i < offset ∨ offset+len ≤ i) :
    u.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  obtain ⟨j,hj,eq⟩ := covers c hc _ ha
  rw [BitVec.add_assoc,← BitVec.ofNat_add] at eq
  have h := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : offset+j < 2^64)] at h
  omega

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
