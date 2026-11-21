import P256.Proofs.Projective.Double.CrossTerms.Memory
import P256.Proofs.Projective.Double.Values
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

namespace Products

structure MovePre (ip : BitVec 64) (reads writes : List (BitVec 64)) (s : RamState) : Prop where
  rip : s.RIP = ip
  readable : ∀ i ∈ reads, MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ writes, P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ writes, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len


end Products
end P256.Proofs.Projective.Double
