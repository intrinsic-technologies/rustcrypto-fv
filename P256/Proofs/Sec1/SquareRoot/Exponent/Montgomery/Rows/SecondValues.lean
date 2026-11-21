import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.States

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem secondStart_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (secondStartEffect p s).Holds s t) (hs : SecondState s w a b) :
    SecondStartState t w a b := by
  have hrsp := Reduction.scratch_rsp (secondStart_frame h)
  refine ⟨secondStart_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, digit, first, second, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowCarry, startCarry, rowQ, add64, adc64, product64, addSpec_low, BitVec.mul_one, addSpec_carry_comm, BitVec.add_comm]

theorem secondMiddle_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (secondMiddleEffect p s).Holds s t) (hs : SecondStartState s w a b) :
    SecondMiddleState t w a b := by
  have hrsp := Reduction.scratch_rsp (secondMiddle_frame h)
  refine ⟨secondMiddle_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, digit, q, c0, c1, x0, x1, second, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowMiddle, middleCarry, add64, adc64, product64, addSpec_low]

theorem secondHigh_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (secondHighEffect p s).Holds s t) (hs : SecondMiddleState s w a b) :
    SecondHighState t w a b := by
  have hrsp := Reduction.scratch_rsp (secondHigh_frame h)
  refine ⟨secondHigh_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, q, m0, m1, m2, x0, x1, low, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, rowCore_eq, middleCarry, add64, adc64, product64, addSpec_low]

theorem secondTop_values {p : BitVec 64} {s t : RamState}
    {w : InterleavedWords} {a next : BitVec 64} {b : Vector (BitVec 64) 4}
    (h : (secondTopEffect p s).Holds s t) (hs : SecondHighState s w a b)
    (hn : (Operand.mem (savedPtr s+16#64) : Operand 64).read s = next) :
    ThirdState t (nextRow w a next b) next b := by
  have hrsp := Reduction.scratch_rsp (secondTop_frame h)
  refine ⟨secondTop_saved h hs.saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rcases hs with ⟨saved, c0, c1, c2, c3, mid, high, carry⟩
  all_goals rcases saved with ⟨b0, b1, b2, b3, p0, p1, p2, p3, inverse⟩
  all_goals simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 p0 p1 p2 p3 inverse
  all_goals
    try rw [hrsp]
    rw [secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    try simp only [← stackPtr_read]
    simp only [savedPtr, BitVec.ofNat_eq_ofNat] at hn
    try simp only [*]
  all_goals
    simp only [BitVec.ofNat_eq_ofNat, nextRow_eq, mergeTop, product64, add64, adc64, addSpec_low,
      boolByte_carry, boolByte_width, boolByte_eq]

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
