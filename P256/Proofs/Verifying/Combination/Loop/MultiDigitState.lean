import P256.Proofs.Verifying.Combination.Loop.MultiRoundState
import P256.Proofs.Verifying.Combination.Algebra.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Proofs.Projective P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure DigitData [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v k : Nat) (point : Projective) (left : Bool) : Prop
    extends RoundData s t tables digits p q u v k point where
  cursor : t.regValue .r13 = digits + (if left then 0 else 272) + BitVec.ofNat 64 (k+7)
  tableCursor : t.regValue .rbp = tables + (if left then 0 else 768)
  remaining : t.regValue .r12 = (if left then 2 else 1)
  savedCursor : memLoad t.external (stackPtr s - 376) 64 = digits + BitVec.ofNat 64 (k+7)

structure DigitState [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v k : Nat) (point : Projective) (left : Bool)
    (address : BitVec 64 := 0x10f2cf) : Prop extends DigitData s t tables digits p q u v k point left where
  rip : t.RIP = address
  identity : (t.regValue .r14).getLsbD 0 = false → point = Projective.identity

structure SelectedState [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v k : Nat) (point selected : Projective) (left : Bool) : Prop
    extends DigitData s t tables digits p q u v k point left where
  rip : t.RIP = 0x10f2a8
  selectedValue : ProjectiveAt t (stackPtr s - 144) selected

def NegativeCorrect : Prop :=
  ∀ [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (tables digits : BitVec 64) (p q point : Projective) (u v k : Nat) (left : Bool) (digit : Int),
    MultiPre s boundary tables digits → DigitData s t tables digits p q u v k point left →
    t.RIP = 0x10f1d0 → t.regValue .rdi = (BitVec.ofInt 8 digit).setWidth 64 →
    (t.regValue .rax).setWidth 8 = BitVec.ofInt 8 digit → Naf.ValidDigit digit → digit < 0 →
    ∃ fuel w, Advances boundary fuel t w ∧
      SelectedState s w tables digits p q u v k point
        (Algebra.signedLookup (Table.oddTable (if left then p else q)) digit) left

def SelectionCorrect : Prop :=
  ∀ [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (tables digits : BitVec 64) (p q point : Projective) (u v k : Nat) (left : Bool),
    MultiPre s boundary tables digits → DigitState s t tables digits p q u v (k+1) point left →
    u < 2^256 → v < 2^256 →
    let digit := ((Naf.digits (if left then u else v))[k]?).getD 0
    ∃ fuel w, Advances boundary fuel t w ∧
      ((digit = 0 ∧ DigitState s w tables digits p q u v (k+1) point left 0x10f2b8) ∨
       (digit ≠ 0 ∧ SelectedState s w tables digits p q u v (k+1) point
          (Algebra.signedLookup (Table.oddTable (if left then p else q)) digit) left))

def DoubleCorrect : Prop :=
  ∀ [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (tables digits : BitVec 64) (p q point : Projective) (u v k : Nat),
    MultiPre s boundary tables digits → RoundState s t tables digits p q u v k point →
    ∃ fuel w, Advances boundary fuel t w ∧
      RoundState s w tables digits p q u v k point.double 0x10f1a3

end P256.Proofs.Verifying.Combination.Loop.Multi
