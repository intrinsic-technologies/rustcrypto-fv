import Standards.RFC.MD5
import Init.Data.BitVec.Bitblast
import Std.Tactic

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

theorem choose_xor (x y z : BitVec 32) : ((y ^^^ z) &&& x) ^^^ z = F x y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [F, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem choose_add (x y z : BitVec 32) : (x &&& y) + (~~~x &&& z) = F x y z := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero,
    hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem choose_second_add (x y z : BitVec 32) :
    (x &&& z) + (y &&& ~~~z) = G x y z := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero,
    hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem choose_or (x y z : BitVec 32) :
    (z &&& ~~~x) ||| (x &&& y) = F x y z := by
  simp only [F, BitVec.and_comm, BitVec.or_comm]

theorem word_add_left_comm (a b c : BitVec 32) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

theorem word_xor_left_comm (a b c : BitVec 32) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

macro "md5_word_arithmetic" : tactic => `(tactic| (
  (try simp only [choose_xor, choose_or]) <;>
  simp only [← choose_add, ← choose_second_add,
    BitVec.add_comm, word_add_left_comm, BitVec.add_assoc, BitVec.and_comm,
    H, I, BitVec.xor_comm, BitVec.xor_assoc, word_xor_left_comm,
    BitVec.or_comm, true_and, and_true]))

def operation (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32)
    (x t : BitVec 32) (shift : Nat) (s : Buffer) : Buffer :=
  ⟨s.D, s.B + (s.A + f s.B s.C s.D + x + t).rotateLeft shift, s.B, s.C⟩

def feedForward (initial final : Buffer) : Buffer :=
  ⟨initial.A + final.A, initial.B + final.B,
    initial.C + final.C, initial.D + final.D⟩

end Md5.Proofs.Block.Rounds
