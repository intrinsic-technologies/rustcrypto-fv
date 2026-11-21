import K256.Proofs.Common.CFG.Lemma.IR
import K256.Proofs.Verify.Transfer.Signature.Simulation

namespace K256.Proofs.Verify.Transfer.Signature

open K256.Proofs.CFG

variable {A B V M : Type} {r : Nat}
variable (pair : A → B → Bool) (live : A → Nat) (ret : Nat)

def indexAt (r off j : Nat) := if j < r then j else j + off

def available (r mask j : Nat) := decide (r ≤ j) || mask.testBit j

def Supports (r off mask i j : Nat) : Bool :=
  (i == indexAt r off j) && available r mask j

def Agree (r off mask : Nat) {n m : Nat} (a : Values V n) (b : Values V m) : Prop :=
  ∀ (i : Fin n) (j : Fin m), Supports r off mask i.val j.val = true → a[i] = b[j]

def LocAgree (x : Location V M A (fun _ => r)) (y : Location V M B (fun _ => r)) : Prop :=
  pair x.label y.label = true ∧ x.store = y.store ∧ Agree r 0 (live x.label) x.arguments y.arguments

def OutAgree (x y : Output V M r) : Prop :=
  x.store = y.store ∧ x.tag = y.tag ∧ Agree r 0 ret x.values y.values

end K256.Proofs.Verify.Transfer.Signature
