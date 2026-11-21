import X86Proofs.Program.Effect



namespace X86Proofs


def rorSpec {n : Nat} (old : StatusFlags) (of : Bool) (c : Nat) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x.rotateRight c
  (r, if c = 0 then old else
    { old with CF := r.msb, OF := if c = 1 then r.msb ^^ r.getLsbD (n - 2) else of })


def rorOracleBits (c : Nat) : Nat := if c = 0 ∨ c = 1 then 0 else 1


def rorFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x.rotateRight c
  if c = 0 then .ofStatusFlags old else
    { CF := some r.msb, PF := some old.PF, AF := some old.AF, ZF := some old.ZF,
      SF := some old.SF, OF := if c = 1 then some (r.msb ^^ r.getLsbD (n - 2)) else none }


theorem rorFlags_allows {n : Nat} (old : StatusFlags) (of : Bool) (c : Nat) (x : BitVec n) :
    (rorFlags old c x).Allows (rorSpec old of c x).2 := by
  unfold rorFlags rorSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

end X86Proofs
