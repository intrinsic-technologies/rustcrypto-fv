import P256.Proofs.Verifying.Combination.Table.Interface
import P256.Proofs.Verifying.Combination.Naf.Recoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open P256.Proofs.Projective
open Table (oddTable oddTableEntry)

def DigitValid (digit : Int) : Prop :=
  digit = 0 ∨ digit.natAbs % 2 = 1 ∧ digit.natAbs ≤ 15

def selectMagnitude (table : Fin 8 → Projective) (magnitude : Nat) : Projective :=
  if h : 0 < magnitude ∧ magnitude ≤ 15 ∧ magnitude % 2 = 1 then
    table ⟨magnitude / 2, by omega⟩
  else identity

def signedLookup (table : Fin 8 → Projective) (digit : Int) : Projective :=
  if digit < 0 then (selectMagnitude table digit.natAbs).negate
  else selectMagnitude table digit.natAbs

def addDigit (table : Fin 8 → Projective) (acc : Projective) (digit : Int) : Projective :=
  if digit = 0 then acc else acc.add (signedLookup table digit)

def digitsValid (digits : List (Int × Int)) : Prop :=
  ∀ pair ∈ digits, DigitValid pair.1 ∧ DigitValid pair.2

def firstValue (digits : List (Int × Int)) : Int :=
  digits.foldr (fun pair rest => pair.1 + 2 * rest) 0

def secondValue (digits : List (Int × Int)) : Int :=
  digits.foldr (fun pair rest => pair.2 + 2 * rest) 0

def accumulator (left right : Fin 8 → Projective) (digits : List (Int × Int)) : Projective :=
  digits.foldr (fun pair rest => addDigit right (addDigit left rest.double pair.1) pair.2)
    identity

def pairDigits : List Int → List Int → List (Int × Int)
  | [], [] => []
  | x :: xs, [] => (x, 0) :: pairDigits xs []
  | [], y :: ys => (0, y) :: pairDigits [] ys
  | x :: xs, y :: ys => (x, y) :: pairDigits xs ys

def linearCombination (p q : Projective) (u v : Nat) : Projective :=
  accumulator (oddTable p) (oddTable q) (pairDigits (Naf.digits u) (Naf.digits v))

end P256.Proofs.Verifying.Combination.Algebra
