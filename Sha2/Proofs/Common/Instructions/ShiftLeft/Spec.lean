import X86Proofs.Program.Effect

namespace Sha2.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shlSpec {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x <<< c
  (r, if c = 0 then old else
    { CF := (x <<< (c - 1)).msb, PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then (r.msb != x.msb) else of })

def shlOracleBits (c : Nat) : Nat := if c = 0 then 0 else if c = 1 then 1 else 2

def shlOracleAF (o : X86.Runtime.Oracle) (c : Nat) : Bool :=
  if c = 1 then oracleBit o else oracleBit (oracleSkip o 1)

def shlFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) : StatusFlagsOutcome :=
  let r := x <<< c
  if c = 0 then .ofStatusFlags old else
    { CF := some ((x <<< (c - 1)).msb), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some (r.msb != x.msb) else none }

theorem shlFlags_allows {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec n) :
    (shlFlags old c x).Allows (shlSpec old of af c x).2 := by
  unfold shlFlags shlSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

end Sha2.Proofs.Common.Instructions.ShiftLeft
