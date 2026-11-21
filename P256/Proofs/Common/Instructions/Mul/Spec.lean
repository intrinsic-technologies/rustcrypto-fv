import X86Proofs.Core.Operand
import X86Proofs.Program.Effect

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

def mulHigh64 (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (a.toNat * b.toNat / 2^64)

theorem mulHigh64_eq_ofInt (a b : BitVec 64) :
    mulHigh64 a b = BitVec.ofInt 64 ((a.toNat : Int) * b.toNat / 2^64) := by
  unfold mulHigh64
  rw [← BitVec.ofInt_natCast, Int.natCast_ediv, Int.natCast_mul]
  rfl

def mulFlags64 (a b : BitVec 64) : StatusFlagsOutcome :=
  let overflow := mulHigh64 a b != 0
  { CF := some overflow, OF := some overflow,
    SF := none, ZF := none, AF := none, PF := none }

def mulStatus64 (o : X86.Runtime.Oracle) (a b : BitVec 64) : StatusFlags :=
  let overflow := mulHigh64 a b != 0
  { CF := overflow, OF := overflow,
    SF := oracleBit o, ZF := oracleBit (oracleSkip o 1),
    AF := oracleBit (oracleSkip o 2), PF := oracleBit (oracleSkip o 3) }

def mulResult64 {σ : Type} (s : X86.State σ) (src : BitVec 64) : X86.State σ :=
  let a : BitVec 64 := s.GPR[gprIndex 0]
  setFlags { s with
    GPR := Vector.set (Vector.set s.GPR (gprIndex 0) (a * src)) (gprIndex 2) (mulHigh64 a src)
    oracle := oracleSkip s.oracle 4 } (mulStatus64 s.oracle a src)

def mulR64Effect (p : BitVec 64) (src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg 0 : Operand 64), a * b⟩,
      ⟨(Operand.reg 2 : Operand 64), mulHigh64 a b⟩]
    flags := some (mulFlags64 a b) }

theorem mulFlags64_allows (o : X86.Runtime.Oracle) (a b : BitVec 64) :
    (mulFlags64 a b).Allows (mulStatus64 o a b) := by
  exact ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

theorem mulR64Effect_components (p : BitVec 64) (src : BitVec 5) (s : RamState) :
    (mulR64Effect p src s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem mulR64Effect_avoids (p : BitVec 64) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (mulR64Effect p src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [mulR64Effect_components, Component.Covers]) code

end P256.Proofs.Common.Instructions
