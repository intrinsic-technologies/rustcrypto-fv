import P256.Proofs.Nonce.Fill.Entry
import P256.Proofs.Nonce.Fill.Generate
import P256.Proofs.Nonce.Fill.Update
import P256.Proofs.Nonce.Fill.Tail
import P256.Proofs.Common.Machine.Divergence

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Machine P256.Proofs.Signing.Search

theorem loop_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state final : State} {nonce : Nat}
    (pre : Pre initial boundary orderAddress original)
    (input : Loop initial s orderAddress state) (search : FirstValid state nonce final) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReturnState initial t orderAddress nonce final := by
  induction search generalizing s with
  | accept state valid =>
    obtain ⟨steps, t, _, run, generated⟩ := generate pre input
    obtain ⟨more, u, advance, updated⟩ := Update.correct pre generated
    obtain ⟨tail, v, finish, result⟩ := tail_accept pre updated valid
    exact ⟨steps + more + tail, v, (run.trans advance).trans finish, result⟩
  | reject state invalid _ ih =>
    obtain ⟨steps, t, _, run, generated⟩ := generate pre input
    obtain ⟨more, u, advance, updated⟩ := Update.correct pre generated
    obtain ⟨tail, v, finish, next⟩ := tail_reject pre updated invalid
    obtain ⟨rest, w, remainder, result⟩ := ih next
    exact ⟨steps + more + tail + rest, w,
      ((run.trans advance).trans finish).trans remainder, result⟩

theorem loop_diverges [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Loop initial s orderAddress state)
    (noValid : ¬ ∃ nonce final, FirstValid state nonce final) :
    Prelude.Diverges boundary s [] := by
  let invariant := fun t => ∃ state, Loop initial t orderAddress state ∧
    ¬ ∃ nonce final, FirstValid state nonce final
  apply diverges_of_progress (invariant := invariant) ?_ ⟨state, input, noValid⟩
  intro t ht
  obtain ⟨current, currentInput, none⟩ := ht
  have invalid : ¬ ValidNonce (nextCandidate current).1 := by
    intro valid
    exact none ⟨_, _, FirstValid.accept current valid⟩
  have nextNone : ¬ ∃ nonce final, FirstValid (nextState current) nonce final := by
    rintro ⟨nonce, final, rest⟩
    exact none ⟨nonce, final, FirstValid.reject current invalid rest⟩
  obtain ⟨steps, u, positive, run, generated⟩ := generate pre currentInput
  obtain ⟨more, v, advance, updated⟩ := Update.correct pre generated
  obtain ⟨tail, w, finish, next⟩ := tail_reject pre updated invalid
  exact Or.inl ⟨steps + more + tail, w, by omega,
    (run.trans advance).trans finish, nextState current, next, nextNone⟩

theorem fill_correct [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original final : State} {nonce : Nat}
    (pre : Pre initial boundary orderAddress original)
    (search : FirstValid original nonce final) :
    ∃ t, Result initial t boundary orderAddress nonce final := by
  obtain ⟨steps, s, run, input⟩ := entry pre
  obtain ⟨rest, t, finish, result⟩ := loop_correct pre input search
  exact ⟨t, { result with execution := ⟨steps + rest, run.trans finish⟩ }⟩

theorem fill_diverges [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original : State}
    (pre : Pre initial boundary orderAddress original)
    (noValid : ¬ ∃ nonce final, FirstValid original nonce final) :
    Prelude.Diverges boundary initial [] := by
  obtain ⟨steps, s, run, input⟩ := entry pre
  exact diverges_of_advances run (loop_diverges pre input noValid)

end P256.Proofs.Nonce.Fill
