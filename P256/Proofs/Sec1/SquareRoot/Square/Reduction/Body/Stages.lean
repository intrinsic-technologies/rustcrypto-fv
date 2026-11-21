import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Inputs

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Field.Montgomery (reduceStep reduceFour)

abbrev slot (s t : RamState) (offset : Nat) : BitVec 64 :=
  memLoad t.external (stackPtr s - 112 + BitVec.ofNat 64 offset) 64

abbrev carryByte (s t : RamState) : BitVec 8 :=
  memLoad t.external (stackPtr s - 112 + 7) 8

structure ModulusSlots (s t : RamState) : Prop where
  p0 : slot s t 56 = 0xffffffffffffffff
  p1 : slot s t 48 = 0xffffffff
  p2 : slot s t 40 = 0
  p3 : slot s t 32 = 0xffffffff00000001

structure First [Bindings] (s t : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x113490
  slots : ModulusSlots s t
  inverse : slot s t 16 = 1
  rcx : t.regValue .rcx = 1
  rsi : t.regValue .rsi = s.regValue .rsi
  rdi : t.regValue .rdi = s.regValue .rdi
  rbp : t.regValue .rbp = 0xffffffffffffffff
  r13 : t.regValue .r13 = 0xffffffff
  value : (t.regValue .r14).toNat + 2^64 * (t.regValue .r15).toNat +
    2^128 * (t.regValue .r11).toNat + 2^192 * (t.regValue .rbx).toNat +
    2^192 * (v / 2^256) = reduceStep v

structure Second [Bindings] (s t : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x11350e
  slots : ModulusSlots s t
  inverse : slot s t 16 = 1
  inputPointer : slot s t 24 = s.regValue .rsi
  rdi : t.regValue .rdi = s.regValue .rdi
  r10 : t.regValue .r10 = 0
  carry : (carryByte s t).toNat ≤ 1
  value : (t.regValue .r13).toNat + 2^64 * (t.regValue .rbp).toNat +
    2^128 * (t.regValue .rbx).toNat + 2^192 * (t.regValue .r14).toNat +
    2^192 * (t.regValue .r9).toNat + 2^256 * (carryByte s t).toNat +
    2^256 * (v / 2^384) = reduceStep (reduceStep v)

structure Third [Bindings] (s t : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x11358d
  slots : ModulusSlots s t
  inverse : slot s t 16 = 1
  inputPointer : slot s t 24 = s.regValue .rsi
  rdi : t.regValue .rdi = s.regValue .rdi
  rsi : t.regValue .rsi = 0xffffffff
  rbp : t.regValue .rbp = 0xffffffff00000001
  carry : (carryByte s t).toNat ≤ 1
  value : (t.regValue .r12).toNat + 2^64 * (t.regValue .r15).toNat +
    2^128 * (t.regValue .r13).toNat + 2^192 * (t.regValue .r9).toNat +
    2^256 * (carryByte s t).toNat + 2^192 * (v / 2^384) =
      reduceStep (reduceStep (reduceStep v))

structure Fourth [Bindings] (s t : RamState) (v : Nat) : Prop where
  frame : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x113627
  slots : ModulusSlots s t
  rdi : t.regValue .rdi = s.regValue .rdi
  r11 : t.regValue .r11 = 0xffffffffffffffff
  top : (t.regValue .rdx).toNat + (slot s t 24).toNat +
    2^64 * (slot s t 16).toNat =
      (t.regValue .rax).toNat + 2^64 * (t.regValue .r12).toNat
  value : (t.regValue .rbx).toNat + 2^64 * (t.regValue .rcx).toNat +
    2^128 * (t.regValue .r8).toNat + 2^192 * (t.regValue .rax).toNat +
    2^256 * (t.regValue .r12).toNat = reduceFour v

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
