import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def rowQ (w : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :=
  add64 (product64 a b[0]).1 w.first

def rowCarry (w : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :=
  startCarry (rowQ w a b).1 (product64 a b[0]).2 (rowQ w a b).2

def rowMiddle (w : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :=
  middleCarry a b[1] (rowQ w a b).1 0 w.second (rowCarry w a b).1 (rowCarry w a b).2

def rowCore (w : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :=
  coreWords w.first w.second w.top.low a b

theorem addSpec_carry_comm (a b : BitVec 64) : (addSpec a b).2.CF = (addSpec b a).2.CF := by
  simpa only [add64] using congrArg Prod.snd (add64_comm a b)

structure SecondState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  digit : (Operand.reg 14#5 : Operand 64).read s = a
  first : (Operand.reg 10#5 : Operand 64).read s = w.first
  second : (Operand.reg 3#5 : Operand 64).read s = w.second
  low : (Operand.reg 15#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid
  high : (Operand.mem (stackPtr s+104#64) : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure ThirdState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  digit : (Operand.reg 12#5 : Operand 64).read s = a
  first : (Operand.reg 11#5 : Operand 64).read s = w.first
  second : (Operand.mem (stackPtr s+56#64) : Operand 64).read s = w.second
  low : (Operand.reg 14#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 1#5 : Operand 64).read s = w.top.mid
  high : (Operand.reg 15#5 : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure FourthState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  digit : (Operand.reg 6#5 : Operand 64).read s = a
  first : (Operand.reg 3#5 : Operand 64).read s = w.first
  second : (Operand.reg 11#5 : Operand 64).read s = w.second
  low : (Operand.reg 10#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid
  high : (Operand.reg 14#5 : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+24#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure SecondStartState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  digit : (Operand.reg 14#5 : Operand 64).read s = a
  q : (Operand.reg 1#5 : Operand 64).read s = (rowQ w a b).1
  c0 : (Operand.reg 5#5 : Operand 64).read s = (rowCarry w a b).1
  c1 : (Operand.reg 13#5 : Operand 64).read s = (rowCarry w a b).2
  x0 : (Operand.reg 11#5 : Operand 64).read s = (product64 a b[1]).1
  x1 : (Operand.mem (stackPtr s+56#64) : Operand 64).read s = (product64 a b[1]).2
  second : (Operand.reg 3#5 : Operand 64).read s = w.second
  low : (Operand.reg 15#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid
  high : (Operand.mem (stackPtr s+104#64) : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure SecondMiddleState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  q : (Operand.reg 1#5 : Operand 64).read s = (rowQ w a b).1
  m0 : (Operand.reg 11#5 : Operand 64).read s = (rowMiddle w a b).1
  m1 : (Operand.reg 10#5 : Operand 64).read s = (rowMiddle w a b).2.1
  m2 : (Operand.reg 6#5 : Operand 64).read s = (rowMiddle w a b).2.2
  x0 : (Operand.reg 8#5 : Operand 64).read s = (product64 a b[2]).1
  x1 : (Operand.reg 12#5 : Operand 64).read s = (product64 a b[2]).2
  low : (Operand.reg 15#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid
  high : (Operand.mem (stackPtr s+104#64) : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure SecondHighState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  c0 : (Operand.reg 11#5 : Operand 64).read s = (rowCore w a b).first
  c1 : (Operand.mem (stackPtr s+56#64) : Operand 64).read s = (rowCore w a b).second
  c2 : (Operand.reg 14#5 : Operand 64).read s = (rowCore w a b).low
  c3 : (Operand.reg 1#5 : Operand 64).read s = (rowCore w a b).high
  mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid
  high : (Operand.mem (stackPtr s+104#64) : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure ThirdStartState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  digit : (Operand.reg 12#5 : Operand 64).read s = a
  q : (Operand.reg 9#5 : Operand 64).read s = (rowQ w a b).1
  c0 : (Operand.reg 5#5 : Operand 64).read s = (rowCarry w a b).1
  c1 : (Operand.reg 13#5 : Operand 64).read s = (rowCarry w a b).2
  x0 : (Operand.reg 3#5 : Operand 64).read s = (product64 a b[1]).1
  x1 : (Operand.reg 10#5 : Operand 64).read s = (product64 a b[1]).2
  second : (Operand.mem (stackPtr s+56#64) : Operand 64).read s = w.second
  low : (Operand.reg 14#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 1#5 : Operand 64).read s = w.top.mid
  high : (Operand.reg 15#5 : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure ThirdMiddleState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  q : (Operand.reg 9#5 : Operand 64).read s = (rowQ w a b).1
  m0 : (Operand.reg 3#5 : Operand 64).read s = (rowMiddle w a b).1
  m1 : (Operand.reg 12#5 : Operand 64).read s = (rowMiddle w a b).2.1
  m2 : (Operand.reg 6#5 : Operand 64).read s = (rowMiddle w a b).2.2
  x0 : (Operand.reg 11#5 : Operand 64).read s = (product64 a b[2]).1
  x1 : (Operand.reg 8#5 : Operand 64).read s = (product64 a b[2]).2
  low : (Operand.reg 14#5 : Operand 64).read s = w.top.low
  mid : (Operand.reg 1#5 : Operand 64).read s = w.top.mid
  high : (Operand.reg 15#5 : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

structure ThirdHighState (s : RamState) (w : InterleavedWords) (a : BitVec 64)
    (b : Vector (BitVec 64) 4) : Prop where
  saved : Saved s b
  c0 : (Operand.reg 3#5 : Operand 64).read s = (rowCore w a b).first
  c1 : (Operand.reg 11#5 : Operand 64).read s = (rowCore w a b).second
  c2 : (Operand.reg 10#5 : Operand 64).read s = (rowCore w a b).low
  c3 : (Operand.reg 9#5 : Operand 64).read s = (rowCore w a b).high
  mid : (Operand.reg 1#5 : Operand 64).read s = w.top.mid
  high : (Operand.reg 15#5 : Operand 64).read s = w.top.high
  carry : (Operand.mem (stackPtr s+7#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat

theorem rowCore_eq (w : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :
    rowCore w a b =
      let m := rowMiddle w a b
      let n := middleCarry a b[2] (rowQ w a b).1 0xffffffff00000001 w.top.low m.2.1 m.2.2
      ⟨m.1, n.1, n.2.1, n.2.2⟩ := rfl

theorem nextRow_eq (w : InterleavedWords) (a next : BitVec 64) (b : Vector (BitVec 64) 4) :
    nextRow w a next b =
      let c := rowCore w a b
      ⟨c.first, c.second, mergeTop c.low c.high w.top.mid w.top.high w.top.carry next b[3]⟩ := rfl

theorem boolByte_width (c : Bool) :
    (BitVec.ofNat 8 c.toNat).setWidth 64 = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

theorem boolByte_eq (c : Bool) :
    (if c then 1#8 else 0#8) = BitVec.ofNat 8 c.toNat := by
  cases c <;> rfl

theorem boolByte_carry (c : Bool) :
    (addSpec (BitVec.ofNat 8 c.toNat) 255#8).2.CF = c := by
  cases c <;> decide +kernel

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
