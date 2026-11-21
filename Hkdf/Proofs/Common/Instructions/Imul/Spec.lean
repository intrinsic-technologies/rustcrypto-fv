import X86Proofs.Core.Operand
import X86Proofs.Program.Effect

set_option autoImplicit false

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

def imulOverflow64 (a b : BitVec 64) : Bool :=
  decide ((a * b).toInt ≠ a.toInt * b.toInt)

def imulSpec64 (o : X86.Runtime.Oracle) (a b : BitVec 64) : BitVec 64 × StatusFlags :=
  (a * b, { CF := imulOverflow64 a b, OF := imulOverflow64 a b,
            SF := oracleBit o, ZF := oracleBit (oracleSkip o 1),
            AF := oracleBit (oracleSkip o 2), PF := oracleBit (oracleSkip o 3) })

def imulFlags64 (a b : BitVec 64) : StatusFlagsOutcome :=
  { CF := some (imulOverflow64 a b), OF := some (imulOverflow64 a b),
    SF := none, ZF := none, AF := none, PF := none }

theorem imulFlags64_allows (o : X86.Runtime.Oracle) (a b : BitVec 64) :
    (imulFlags64 a b).Allows (imulSpec64 o a b).2 :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

def imulR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), a * b⟩]
    flags := some (imulFlags64 a b) }

theorem imulR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (imulR64R64Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem imulR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (imulR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [imulR64R64Effect_components, Component.Covers]) code

end Hkdf.Proofs.Common.Instructions
