import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Initialize
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.ByteMemory
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Carry
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.EffectCompose.Multiply
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Instructions.AddByte.Legacy
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BlockPre (p : BitVec 64) (size : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart ((Operand.reg 4#5 : Operand 64).read s) 112 p size

structure TopPre (p : BitVec 64) (size : Nat) (s : RamState) : Prop extends BlockPre p size s where
  input : MemReadable s ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s+24#64) : Operand 64).read s) 32

theorem addSpec_low {n : Nat} (a b : BitVec n) : (addSpec a b).1 = a+b := rfl

theorem restore_carry (c : Bool) : (addSpec (if c then 1#8 else 0#8) 255#8).2.CF = c := by
  cases c <;> decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
