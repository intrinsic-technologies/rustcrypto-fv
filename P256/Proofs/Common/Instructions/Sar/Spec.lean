import X86Proofs.Program.Effect

namespace P256.Proofs.Common.Instructions

open X86Proofs

def sarSpec {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x.sshiftRight c
  (r, if c = 0 then old else
    { CF := x.getLsbD (c - 1), PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then false else of })

def sarOracleBits (c : Nat) : Nat := if c = 0 then 0 else if c = 1 then 1 else 2

def sarOracleAF (o : X86.Runtime.Oracle) (c : Nat) : Bool :=
  if c = 1 then oracleBit o else oracleBit (oracleSkip o 1)

def sarFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x.sshiftRight c
  if c = 0 then .ofStatusFlags old else
    { CF := some (x.getLsbD (c - 1)), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some false else none }

theorem sarFlags_allows {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) :
    (sarFlags old c x).Allows (sarSpec old of af c x).2 := by
  unfold sarFlags sarSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

end P256.Proofs.Common.Instructions
