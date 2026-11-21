import P256.Proofs.Field.Montgomery.Words

set_option autoImplicit false

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)


def addWord (a b c : Nat) : Nat × Nat :=
  let t := a+b+c
  (t % wordBase, t / wordBase)

theorem addWord_eq (a b c : Nat) :
    (addWord a b c).1 + wordBase * (addWord a b c).2 = a+b+c := by
  exact Nat.mod_add_div _ _

theorem addWord_low_lt (a b c : Nat) : (addWord a b c).1 < wordBase :=
  Nat.mod_lt _ (by decide)

theorem addWord_high_le_one {a b c : Nat}
    (ha : a < wordBase) (hb : b < wordBase) (hc : c ≤ 1) :
    (addWord a b c).2 ≤ 1 := by
  dsimp [addWord, wordBase] at *
  omega

theorem mulWord_bound {a b : Nat} (ha : a < wordBase) (hb : b < wordBase) :
    a*b ≤ (wordBase-1)*(wordBase-1) :=
  Nat.mul_le_mul (by omega) (by omega)

theorem mulWord_high_lt {a b : Nat} (ha : a < wordBase) (hb : b < wordBase) :
    a*b / wordBase < wordBase-1 := by
  have hp := mulWord_bound ha hb
  dsimp [wordBase] at *
  omega

def addProduct (p c d : Nat) : Nat × Nat :=
  let low1 := addWord (p % wordBase) c 0
  let high1 := addWord (p / wordBase) 0 low1.2
  let low2 := addWord low1.1 d 0
  let high2 := addWord high1.1 0 low2.2
  (low2.1, high2.1)

theorem addProduct_eq {p c d : Nat}
    (hp : p ≤ (wordBase-1)*(wordBase-1))
    (hc : c < wordBase) (hd : d < wordBase) :
    (addProduct p c d).1 + wordBase * (addProduct p c d).2 = p+c+d := by
  dsimp [addProduct, addWord, wordBase] at *
  omega

theorem addProduct_low_lt (p c d : Nat) : (addProduct p c d).1 < wordBase :=
  addWord_low_lt _ _ _

theorem addProduct_high_lt (p c d : Nat) : (addProduct p c d).2 < wordBase :=
  addWord_low_lt _ _ _

end P256.Proofs.Field.Schoolbook
