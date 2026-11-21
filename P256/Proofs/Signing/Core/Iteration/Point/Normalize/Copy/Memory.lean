import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem byte {s t u : RamState} {offset i : Nat}
    (agrees : AgreesExcept (ScalarFrame.Copy32.components (frameBase s+BitVec.ofNat 64 offset)) t u)
    (bound : offset+32 ≤ 2232) (small : i < 2^64)
    (apart : i < offset ∨ offset+32 ≤ i) :
    u.external[frameBase s+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc ha
  simp only [ScalarFrame.Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  obtain ⟨j,hj,eq⟩ := ha
  rw [BitVec.add_assoc,← BitVec.ofNat_add] at eq
  have h := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : offset+j < 2^64)] at h
  omega

theorem preserved {s t u : RamState} {offset : Nat}
    (agrees : AgreesExcept (ScalarFrame.Copy32.components (frameBase s+BitVec.ofNat 64 offset)) t u)
    (bound : offset+32 ≤ 2232)
    (apart : ∀ i, LiveOffset i → i < offset ∨ offset+32 ≤ i) : Preserved s t u := by
  intro i live
  exact byte agrees bound (by rcases live with h|h|h|h <;> omega) (apart i live)

theorem montgomery {s t u : RamState} {offset source x : Nat}
    (agrees : AgreesExcept (ScalarFrame.Copy32.components (frameBase s+BitVec.ofNat 64 offset)) t u)
    (bound : offset+32 ≤ 2232) (sourceBound : source+32 ≤ 2232)
    (apart : source+32 ≤ offset ∨ offset+32 ≤ source)
    (value : Field.MontgomeryAt t (frameBase s+BitVec.ofNat 64 source) x) :
    Field.MontgomeryAt u (frameBase s+BitVec.ofNat 64 source) x := by
  apply value.of_bytes_eq
  intro i hi
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
    byte agrees bound (i := source+i) (by omega) (by omega)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy
