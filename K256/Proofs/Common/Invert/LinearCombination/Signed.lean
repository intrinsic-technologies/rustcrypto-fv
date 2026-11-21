import K256.Proofs.Common.Invert.LinearCombination.Wide

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

def selectedRight (b : Vector (BitVec 64) 5) (sa sb : Bool) : Vector (BitVec 64) 5 :=
  if sa = sb then negateWide b else b

def coreDifference (a b : Vector (BitVec 64) 5) (sa sb : Bool) :=
  subtractWide a (selectedRight b sa sb)

def coreFlip (a b : Vector (BitVec 64) 5) (sa sb : Bool) : Bool :=
  (sa != sb) && ((coreDifference a b sa sb).2 != 0)

def coreMagnitude (a b : Vector (BitVec 64) 5) (sa sb : Bool) : Vector (BitVec 64) 5 :=
  if coreFlip a b sa sb then negateWide (coreDifference a b sa sb).1
  else (coreDifference a b sa sb).1

def coreNegative (a b : Vector (BitVec 64) 5) (sa sb : Bool) : Bool :=
  if coreFlip a b sa sb then sb else sa

theorem subtractWide_negate_value (a b : Vector (BitVec 64) 5)
    (bound : wideValue a + wideValue b < 2^320) :
    wideValue (subtractWide a (negateWide b)).1 = wideValue a + wideValue b := by
  have sub := subtractWide_value a (negateWide b)
  have neg := negateWide_value b
  have resultBound := wideValue_lt (subtractWide a (negateWide b)).1
  split at neg <;> omega

theorem signed_core_value (a b : Vector (BitVec 64) 5) (sa sb : Bool)
    (bound : wideValue a + wideValue b < 2^320) :
    signedWideValue a sa + signedWideValue b sb =
      signedWideValue (coreMagnitude a b sa sb) (coreNegative a b sa sb) := by
  have same := subtractWide_negate_value a b bound
  have sub := subtractWide_value a b
  have resultBound := wideValue_lt (subtractWide a b).1
  have aBound := wideValue_lt a
  have bBound := wideValue_lt b
  have neg := negateWide_value (subtractWide a b).1
  have borrow := eq_zero_or_one sub.1
  rcases borrow with borrow | borrow <;>
    cases sa <;> cases sb <;>
    simp only [coreMagnitude,coreNegative,coreFlip,coreDifference,selectedRight,
      Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,
      show (false != false) = false from rfl, show (true != true) = false from rfl,
      show (false != true) = true from rfl, show (true != false) = true from rfl,
      Bool.false_and,Bool.true_and,borrow,show ((0 : BitVec 64) != 0) = false from rfl,
      show ((1 : BitVec 64) != 0) = true from rfl,signedWideValue,
      same] <;>
    simp only [borrow, show (0 : BitVec 64).toNat = 0 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl] at sub <;>
    split at neg <;> omega

end K256.Proofs.Common.Invert.LinearCombination
