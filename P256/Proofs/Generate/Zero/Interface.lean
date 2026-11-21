import P256.Proofs.Program.Interface
import X86Proofs.Instructions.Call.Triple
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation
import P256.Proofs.Generate.Zero.Arguments

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def prefixClobbers (s : RamState) : List Component :=
  [.mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 8, .reg 9, .reg 10, .flags, .rip]

def clobbers (s : RamState) : List Component :=
  prefixClobbers s ++ [.reg 7, .mem (stackPtr s - 1) 1]

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (x y : Nat),
    CalleePre s boundary 0x1132c0 32 32 32 →
    SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rdi) x →
    SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) y →
    ∃ t, CalleeResult s t boundary 32 32 ∧
      (t.regValue .rax).setWidth 8 = (if x = y then 1 else 0) ∧
      AgreesExcept (clobbers s) s t ∧ MemoryWriteFrame s t #v[Stack.region s 32]

structure PrefixCode (offset : Nat) (disp : BitVec 32) : Prop where
  bound : offset + 19 < 118431
  push : Extracted.textBytes.toListFrom offset 1 = [0x50]
  arguments : Extracted.textBytes.toListFrom (offset + 1) argumentBytes.length = argumentBytes
  call : Extracted.textBytes.toListFrom (offset + 14) 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 (offset + 14)) 5
    (disp.signExtend 64) = 0x119270

structure PrefixResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (offset : Nat) (x y : Nat) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  agrees : AgreesExcept (prefixClobbers s) s t
  rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 19)
  rsp : stackPtr t = stackPtr s - 8
  value : (t.regValue .rax).setWidth 8 = if x = y then 1 else 0

end P256.Proofs.Generate.Zero
