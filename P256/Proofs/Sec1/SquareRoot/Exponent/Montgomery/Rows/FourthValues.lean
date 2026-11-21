import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.States
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fourthRow_values
    {p0 p1 p2 p3 : BitVec 64} {s s1 s2 s3 t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (hs : Saved s b)
    (digit : (Operand.reg 6#5 : Operand 64).read s = a)
    (first : (Operand.reg 3#5 : Operand 64).read s = w.first)
    (second : (Operand.reg 11#5 : Operand 64).read s = w.second)
    (low : (Operand.reg 10#5 : Operand 64).read s = w.top.low)
    (mid : (Operand.reg 9#5 : Operand 64).read s = w.top.mid)
    (high : (Operand.reg 14#5 : Operand 64).read s = w.top.high)
    (carry : (Operand.mem (stackPtr s+24#64) : Operand 8).read s = BitVec.ofNat 8 w.top.carry.toNat)
    (e1 : (fourthStartEffect p0 s).Holds s s1)
    (e2 : (fourthMiddleEffect p1 s1).Holds s1 s2)
    (e3 : (fourthHighEffect p2 s2).Holds s2 s3)
    (e4 : (fourthTopEffect p3 s3).Holds s3 t) :
    Reduction.Input t ⟨(lastRow w a b).first, (lastRow w a b).second,
      (lastRow w a b).top.low, (lastRow w a b).top.mid⟩ (lastRow w a b).top.high ∧
    (Operand.reg 10#5 : Operand 64).read t = (lastRow w a b).top.highBeforeCarry ∧
    (Operand.mem (stackPtr t+16#64) : Operand 8).read t =
      BitVec.ofNat 8 (lastRow w a b).top.carry.toNat ∧
    Reduction.Modulus t Reduction.modulus := by
  have vb0 : (Operand.mem (stackPtr s+72#64) : Operand 64).read s = b[0] := hs.b0
  have vb1 : (Operand.mem (stackPtr s+16#64) : Operand 64).read s = b[1] := hs.b1
  have vb2 : (Operand.mem (stackPtr s+88#64) : Operand 64).read s = b[2] := hs.b2
  have vp0 : (Operand.mem (stackPtr s+32#64) : Operand 64).read s = 0xffffffffffffffff#64 := hs.p0
  have vp1 : (Operand.mem (stackPtr s+48#64) : Operand 64).read s = 0xffffffff#64 := hs.p1
  have vp2 : (Operand.mem (stackPtr s+40#64) : Operand 64).read s = 0#64 := hs.p2
  have vp3 : (Operand.mem (stackPtr s+64#64) : Operand 64).read s = 0xffffffff00000001#64 := hs.p3
  have vinverse : (Operand.mem (stackPtr s+80#64) : Operand 64).read s = 1#64 := hs.inverse
  let q := add64 (product64 a b[0]).1 w.first
  let c := startCarry q.1 (product64 a b[0]).2 q.2
  let m := middleCarry a b[1] q.1 0 w.second c.1 c.2
  let n := middleCarry a b[2] q.1 0xffffffff00000001 w.top.low m.2.1 m.2.2
  let z := finishTop n.2.1 n.2.2 w.top.mid w.top.high w.top.carry
  have start :
    (Operand.reg 6#5 : Operand 64).read s1 = a ∧
    (Operand.reg 15#5 : Operand 64).read s1 = q.1 ∧
    (Operand.reg 12#5 : Operand 64).read s1 = c.1 ∧
    (Operand.reg 8#5 : Operand 64).read s1 = c.2 ∧
    (Operand.reg 1#5 : Operand 64).read s1 = (product64 a b[1]).1 ∧
    (Operand.mem (stackPtr s1+16#64) : Operand 64).read s1 = (product64 a b[1]).2 ∧
    (Operand.reg 11#5 : Operand 64).read s1 = w.second ∧
    (Operand.reg 10#5 : Operand 64).read s1 = w.top.low ∧
    (Operand.reg 9#5 : Operand 64).read s1 = w.top.mid ∧
    (Operand.reg 14#5 : Operand 64).read s1 = w.top.high ∧
    (Operand.mem (stackPtr s1+24#64) : Operand 8).read s1 = BitVec.ofNat 8 w.top.carry.toNat ∧
    (Operand.mem (stackPtr s1+88#64) : Operand 64).read s1 = b[2] ∧
    (Operand.mem (stackPtr s1+32#64) : Operand 64).read s1 = 0xffffffffffffffff#64 ∧
    (Operand.mem (stackPtr s1+48#64) : Operand 64).read s1 = 0xffffffff#64 ∧
    (Operand.mem (stackPtr s1+40#64) : Operand 64).read s1 = 0#64 ∧
    (Operand.mem (stackPtr s1+64#64) : Operand 64).read s1 = 0xffffffff00000001#64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rw [Reduction.scratch_rsp (fourthStart_frame e1)]
    all_goals rw [fourthStart_read e1]
    all_goals x86_norm [fourthStartEffect, stackPtr_read]
    all_goals simp only [← stackPtr_read, digit, first, second, low, mid, high, carry, vb0, vb1, vb2, vp0, vp1, vp2, vp3, vinverse, BitVec.mul_one]
    all_goals try { simp only [c, q, startCarry, add64, adc64, product64, addSpec_carry_comm w.first (a*b[0]), addSpec_low, BitVec.add_comm w.first (a*b[0])] <;> rfl }
  obtain ⟨d1, q1, c01, c11, x01, x11, second1, low1, mid1, high1, carry1, b21, vp01, vp11, vp21, vp31⟩ := start
  have middle :
    (Operand.reg 15#5 : Operand 64).read s2 = q.1 ∧
    (Operand.reg 1#5 : Operand 64).read s2 = m.1 ∧
    (Operand.reg 3#5 : Operand 64).read s2 = m.2.1 ∧
    (Operand.reg 5#5 : Operand 64).read s2 = m.2.2 ∧
    (Operand.reg 6#5 : Operand 64).read s2 = (product64 a b[2]).1 ∧
    (Operand.reg 13#5 : Operand 64).read s2 = (product64 a b[2]).2 ∧
    (Operand.reg 10#5 : Operand 64).read s2 = w.top.low ∧
    (Operand.reg 9#5 : Operand 64).read s2 = w.top.mid ∧
    (Operand.reg 14#5 : Operand 64).read s2 = w.top.high ∧
    (Operand.mem (stackPtr s2+24#64) : Operand 8).read s2 = BitVec.ofNat 8 w.top.carry.toNat ∧
    (Operand.mem (stackPtr s2+32#64) : Operand 64).read s2 = 0xffffffffffffffff#64 ∧
    (Operand.mem (stackPtr s2+48#64) : Operand 64).read s2 = 0xffffffff#64 ∧
    (Operand.mem (stackPtr s2+40#64) : Operand 64).read s2 = 0#64 ∧
    (Operand.mem (stackPtr s2+64#64) : Operand 64).read s2 = 0xffffffff00000001#64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rw [Reduction.scratch_rsp (fourthMiddle_frame e2)]
    all_goals rw [fourthMiddle_read e2]
    all_goals x86_norm [fourthMiddleEffect, stackPtr_read]
    all_goals simp only [← stackPtr_read, d1, q1, c01, c11, x01, x11, second1, low1, mid1, high1, carry1, b21, vp01, vp11, vp21, vp31]
    all_goals try { simp only [m, middleCarry, add64, adc64, product64, addSpec_low] <;> rfl }
  obtain ⟨q2, m02, m12, m22, x02, x12, low2, mid2, high2, carry2, vp02, vp12, vp22, vp32⟩ := middle
  have higher :
    (Operand.reg 1#5 : Operand 64).read s3 = m.1 ∧
    (Operand.reg 6#5 : Operand 64).read s3 = n.1 ∧
    (Operand.reg 0#5 : Operand 64).read s3 = n.2.1 ∧
    (Operand.reg 2#5 : Operand 64).read s3 = n.2.2 ∧
    (Operand.reg 9#5 : Operand 64).read s3 = w.top.mid ∧
    (Operand.reg 14#5 : Operand 64).read s3 = w.top.high ∧
    (Operand.mem (stackPtr s3+24#64) : Operand 8).read s3 = BitVec.ofNat 8 w.top.carry.toNat ∧
    (Operand.reg 12#5 : Operand 64).read s3 = 0xffffffff00000001#64 ∧
    (Operand.mem (stackPtr s3+32#64) : Operand 64).read s3 = 0xffffffffffffffff#64 ∧
    (Operand.mem (stackPtr s3+48#64) : Operand 64).read s3 = 0xffffffff#64 ∧
    (Operand.mem (stackPtr s3+40#64) : Operand 64).read s3 = 0#64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rw [Reduction.scratch_rsp (fourthHigh_frame e3)]
    all_goals rw [fourthHigh_read e3]
    all_goals x86_norm [fourthHighEffect, stackPtr_read]
    all_goals simp only [← stackPtr_read, q2, m02, m12, m22, x02, x12, low2, mid2, high2, carry2, vp02, vp12, vp22, vp32]
    all_goals try { simp only [n, middleCarry, add64, adc64, product64, addSpec_low] <;> rfl }
  obtain ⟨m03, n03, n13, n23, mid3, high3, carry3, p33, vp03, vp13, vp23⟩ := higher
  change Reduction.Input t ⟨m.1, n.1, z.low, z.mid⟩ z.high ∧
    (Operand.reg 10#5 : Operand 64).read t = z.highBeforeCarry ∧
    (Operand.mem (stackPtr t+16#64) : Operand 8).read t = BitVec.ofNat 8 z.carry.toNat ∧
    Reduction.Modulus t Reduction.modulus
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals try rw [Reduction.scratch_rsp (fourthTop_frame e4)]
  all_goals rw [fourthTop_read e4]
  all_goals x86_norm [fourthTopEffect, stackPtr_read]
  all_goals simp only [← stackPtr_read, m03, n03, n13, n23, mid3, high3, carry3, p33, vp03, vp13, vp23]
  all_goals simp only [z, finishTop, add64, adc64, addSpec_low, boolByte_width, boolByte_eq, Reduction.modulus]
  all_goals rfl

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
