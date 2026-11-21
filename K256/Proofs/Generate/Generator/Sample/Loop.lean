import K256.Proofs.Generate.Generator.Sample.Prologue
import K256.Proofs.Generate.Generator.Sample.Decode
import K256.Proofs.Generate.Generator.Sample.Decide

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem sample {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ b m d, Run.Reaches ⟨⟨.l105f30, a, fr.original⟩, stack⟩ ⟨⟨.l10607d, b, m⟩, stack⟩ ∧
      K256.Spec.Secp256k1.randomSecret random = some d ∧ Accepted fr d b m := by
  have valid : (K256.Spec.Secp256k1.randomSecret random).isSome := call.inputsHoldValues.1
  obtain ⟨last, d, limit, accepted, rejected⟩ := Sampling.randomSecret_isSome_iff.mp valid
  obtain ⟨b, m, start, inv⟩ := firstBlock call entry (by omega) stack
  let rec run (i : Nat) (hi : i ≤ last) (b : Registers) (m : Ram) (inv : AtBlock s random fr i b m) :
      ∃ c n, Run.Reaches ⟨⟨.l106020, b, m⟩, stack⟩ ⟨⟨.l10607d, c, n⟩, stack⟩ ∧
        Accepted fr d c n := by
    obtain ⟨c, n, steps, afterDecode⟩ := decode call entry (Nat.lt_of_le_of_lt hi limit) inv stack
    have branch := decideBlock call entry (Nat.lt_of_le_of_lt hi limit) afterDecode stack
    by_cases equal : i = last
    · subst i
      rw [accepted] at branch
      obtain ⟨e, p, reach, post⟩ := branch
      exact ⟨e, p, steps.trans reach, post⟩
    · rw [rejected i (by omega)] at branch
      obtain ⟨e, p, reach, next⟩ := branch (by omega)
      obtain ⟨f, q, finish, post⟩ := run (i+1) (by omega) e p next
      exact ⟨f, q, steps.trans (reach.trans finish), post⟩
  termination_by last - i
  obtain ⟨c, n, steps, fin⟩ := run 0 (Nat.zero_le _) b m inv
  exact ⟨c, n, d, start.trans steps, Sampling.randomSecret_of_accepted limit rejected accepted, fin⟩

end K256.Proofs.Generate.Generator.Sample
