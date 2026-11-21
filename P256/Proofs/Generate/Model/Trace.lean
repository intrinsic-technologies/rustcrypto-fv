import P256.Spec.Generate

set_option autoImplicit false

namespace P256.Proofs.Generate

open P256.Spec Standards.SECG.ECC

inductive DrawTrace (bytes : ByteArray) : Nat → Nat → Prop
  | accept {offset d : Nat} : offset + 32 ≤ bytes.size →
      Keys.decodeSecret Operations.domain (bytes.extract offset (offset + 32)) = some d →
      DrawTrace bytes offset d
  | reject {offset d : Nat} : offset + 32 ≤ bytes.size →
      Keys.decodeSecret Operations.domain (bytes.extract offset (offset + 32)) = none →
      DrawTrace bytes (offset + 32) d → DrawTrace bytes offset d

theorem trace_of_go_some {bytes : ByteArray} {fuel offset d : Nat}
    (accepted : Ecdh.firstAccepted.go 32 (Keys.decodeSecret Operations.domain) bytes fuel offset =
      some d) : DrawTrace bytes offset d := by
  induction fuel generalizing offset with
  | zero => simp [Ecdh.firstAccepted.go] at accepted
  | succ fuel ih =>
    simp only [Ecdh.firstAccepted.go] at accepted
    split at accepted
    · rename_i available
      split at accepted
      · rename_i value decoded
        cases accepted
        exact .accept available decoded
      · rename_i decoded
        exact .reject available decoded (ih accepted)
    · contradiction

theorem go_some_of_trace {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) {fuel : Nat}
    (enough : bytes.size < fuel + offset) :
    Ecdh.firstAccepted.go 32 (Keys.decodeSecret Operations.domain) bytes fuel offset = some d := by
  induction trace generalizing fuel with
  | accept available decoded =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [Ecdh.firstAccepted.go, available, decoded]
  | reject available decoded trace ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [Ecdh.firstAccepted.go, ite_eq_left available, decoded]
      exact ih (by omega)

theorem draw_some_iff_trace {bytes : ByteArray} {d : Nat} :
    Ecdh.drawNonzeroScalar bytes = some d ↔ DrawTrace bytes 0 d := by
  constructor
  · exact trace_of_go_some
  · intro trace
    exact go_some_of_trace trace (by omega)

theorem DrawTrace.unique {bytes : ByteArray} {offset d e : Nat}
    (left : DrawTrace bytes offset d) (right : DrawTrace bytes offset e) : d = e := by
  have a := go_some_of_trace left (fuel := bytes.size + 1) (by omega)
  have b := go_some_of_trace right (fuel := bytes.size + 1) (by omega)
  exact Option.some.inj (a.symm.trans b)

theorem DrawTrace.available {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) : offset + 32 ≤ bytes.size := by
  cases trace <;> assumption

theorem DrawTrace.step {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) :
    (Keys.decodeSecret Operations.domain (bytes.extract offset (offset + 32)) = some d) ∨
      (Keys.decodeSecret Operations.domain (bytes.extract offset (offset + 32)) = none ∧
        DrawTrace bytes (offset + 32) d) := by
  cases trace with
  | accept available decoded => exact Or.inl decoded
  | reject available decoded rest => exact Or.inr ⟨decoded, rest⟩

theorem DrawTrace.terminal {bytes : ByteArray} {offset d : Nat}
    (trace : DrawTrace bytes offset d) :
    ∃ k, offset + 32 * (k + 1) ≤ bytes.size ∧
      Keys.decodeSecret Operations.domain
        (bytes.extract (offset + 32 * k) (offset + 32 * (k + 1))) = some d ∧
      ∀ j < k, Keys.decodeSecret Operations.domain
        (bytes.extract (offset + 32 * j) (offset + 32 * (j + 1))) = none := by
  induction trace with
  | accept available decoded =>
    exact ⟨0, by simpa using available, by simpa using decoded, by omega⟩
  | @reject offset d available decoded trace ih =>
    obtain ⟨k, bound, accepted, rejected⟩ := ih
    refine ⟨k + 1, by omega, ?_, ?_⟩
    · simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using accepted
    · intro j hj
      cases j with
      | zero => simpa using decoded
      | succ j =>
        simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using rejected j (by omega)

end P256.Proofs.Generate
