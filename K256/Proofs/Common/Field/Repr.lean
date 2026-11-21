import K256.Spec.Secp256k1

namespace K256.Proofs.Common.Field

abbrev Word := BitVec 64
abbrev Limbs := Vector Word 5
def modulus : Nat := Standards.SECG.DomainParameters.Secp256k1.domain.p
def radix : Nat := 2 ^ 52
def limbValue (a : Limbs) : Nat :=
  (List.range 5).foldl (fun z i => z + (a[i]!).toNat * radix ^ i) 0
def FieldRepr (a : Limbs) (x : Fin modulus) (m : Nat) : Prop :=
  (∀ i : Fin 5,
    if i.val < 4 then (a[i]!).toNat ≤ 2 * m * (2 ^ 52 - 1)
    else (a[i]!).toNat ≤ 2 * m * (2 ^ 48 - 1)) ∧
    limbValue a % modulus = x.val

end K256.Proofs.Common.Field
