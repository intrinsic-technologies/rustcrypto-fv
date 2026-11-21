import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.States

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem thirdStart_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (thirdStartEffect p s).Holds s t) (hs : ThirdState s w a b) :
    ThirdStartState t w a b := by
  have hrsp := Reduction.scratch_rsp (thirdStart_frame h)
  refine ⟨thirdStart_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, digit, first, second, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowCarry, startCarry, rowQ, add64, adc64, product64, addSpec_low, BitVec.mul_one, addSpec_carry_comm, BitVec.add_comm]

theorem thirdMiddle_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (thirdMiddleEffect p s).Holds s t) (hs : ThirdStartState s w a b) :
    ThirdMiddleState t w a b := by
  have hrsp := Reduction.scratch_rsp (thirdMiddle_frame h)
  refine ⟨thirdMiddle_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, digit, q, c0, c1, x0, x1, second, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowMiddle, middleCarry, add64, adc64, product64, addSpec_low]

theorem thirdHigh_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (thirdHighEffect p s).Holds s t) (hs : ThirdMiddleState s w a b) :
    ThirdHighState t w a b := by
  have hrsp := Reduction.scratch_rsp (thirdHigh_frame h)
  refine ⟨thirdHigh_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, q, m0, m1, m2, x0, x1, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowCore_eq, middleCarry, add64, adc64, product64, addSpec_low]

theorem thirdTop_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a next : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (thirdTopEffect p s).Holds s t) (hs : ThirdHighState s w a b)
    (hn : (Operand.mem (savedPtr s+24#64) : Operand 64).read s = next) :
    FourthState t (nextRow w a next b) next b := by
  have hrsp := Reduction.scratch_rsp (thirdTop_frame h)
  refine ⟨thirdTop_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, c0, c1, c2, c3, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    simp only [savedPtr, BitVec.ofNat_eq_ofNat] at hn
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, nextRow_eq, mergeTop, product64, add64, adc64, addSpec_low,
      boolByte_carry, boolByte_width, boolByte_eq]

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
