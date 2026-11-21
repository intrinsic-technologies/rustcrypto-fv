import P256.Proofs.HMAC.Mathematics
import P256.Proofs.Common.Instructions.CrossPageStore.Range
import P256.Proofs.Program.Code
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore

inductive Loop where
  | valueInner | valueOuter
  | updateInner | updateOuter | seededInner | seededOuter
  deriving DecidableEq

def Loop.entry : Loop → Nat
  | .valueInner => 0x10a990 | .valueOuter => 0x10aa40
  | .updateInner => 0x109fd0 | .updateOuter => 0x10a070
  | .seededInner => 0x10a4d0 | .seededOuter => 0x10a570

def Loop.offset : Loop → Nat
  | .valueInner | .valueOuter => 8
  | .updateInner | .updateOuter => 88
  | .seededInner | .seededOuter => 0

def Loop.mask : Loop → UInt8
  | .valueInner | .updateInner | .seededInner => 0x36
  | .valueOuter | .updateOuter | .seededOuter => 0x6a

def Loop.disp (loop : Loop) (i : Nat) : Disp :=
  match loop with
  | .updateInner | .updateOuter => .d8 (BitVec.ofNat 8 (85 + i))
  | .seededInner | .seededOuter => if i = 3 then .none else .d8 (BitVec.ofNat 8 i - 3)
  | _ => .d8 (BitVec.ofNat 8 (loop.offset - 3 + i))

def Loop.mode (loop : Loop) (i : Nat) : AddrMode := .sib 4 (some 0) 0 (loop.disp i)

def Loop.position (loop : Loop) (i : Nat) : Nat :=
  match loop with
  | .updateInner | .updateOuter => 5 * i
  | .seededInner | .seededOuter => if i < 4 then 5 * i else 19
  | _ => 5 * i

def Loop.length (loop : Loop) : Nat := loop.position 4 + 10

def Loop.address (loop : Loop) (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (loop.entry + loop.position i)

def buffer (loop : Loop) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 loop.offset

def footprint (loop : Loop) (s : RamState) : List Component :=
  [.reg 0, .flags, .rip, .mem (buffer loop s) 64]

structure Memory (loop : Loop) (s : RamState) : Prop where
  writable : Writable s (buffer loop s) 64
  avoids : ∀ i < 64, ¬ InProgram (buffer loop s + BitVec.ofNat 64 i)

structure Pre (loop : Loop) (s : RamState) : Prop extends Memory loop s where
  rip : s.RIP = BitVec.ofNat 64 loop.entry
  counter : s.regValue .rax = 3

structure Post (loop : Loop) (s t : RamState) : Prop where
  rip : t.RIP = BitVec.ofNat 64 (loop.entry + loop.length)
  counter : t.regValue .rax = 67
  agrees : AgreesExcept (footprint loop s) s t
  bytes : Bytes t.external (buffer loop s) 64
    (fun i => memByte s.external (buffer loop s + BitVec.ofNat 64 i) ^^^ loop.mask)

end P256.Proofs.HMAC.Pad
