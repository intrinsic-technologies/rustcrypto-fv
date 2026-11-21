import K256.Proofs.Verify.Core.Serializer.Prefix

namespace K256.Proofs.Verify.Core.Serializer

open X86.Machine X86Proofs K256.Proofs.Refine

private theorem prefixStore_word (m : Ram) (dst : BitVec 64) (w : Vector (BitVec 64) 4)
    (k : Nat) (hk : k < 4) :
    prefixStore m dst w (8 * k + 8) =
      memStore (prefixStore m dst w (8 * k)) (dst + BitVec.ofNat 64 (8 * k)) w[k] := by
  let a := dst + BitVec.ofNat 64 (8 * k)
  let s := prefixStore m dst w (8 * k)
  let write (mem : Ram) (i : Nat) :=
    memStore mem (a + BitVec.ofNat 64 i) (w[k].extractLsb' (8 * i) 8)
  have group (n : Nat) (hn : n ≤ 8) :
      prefixStore m dst w (8 * k + n) = (List.range n).foldl write s := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.add_succ, prefixStore.eq_2, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ← ih (by omega)]
      have word : (8 * k + n) / 8 % 4 = k := by omega
      have shift : (8 * k + n) % 8 * 8 = 8 * n := by omega
      simp only [word, shift, write, a, BitVec.add_assoc, BitVec.ofNat_add]
  refine (group 8 (by decide)).trans ?_
  change (List.range 8).foldl write s = memStore s a w[k]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, write]
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a]
  exact storeBytes_eq_memStore s a w[k]

theorem prefix_words (m : Ram) (dst : BitVec 64) (w : Vector (BitVec 64) 4)
    (low : dst.toNat + 32 ≤ 2 ^ 64) : WordsAt (prefixStore m dst w 32) dst 64 w := by
  have h0 : prefixStore m dst w 8 = memStore m dst w[0] := by
    have h := prefixStore_word m dst w 0 (by decide)
    rw [show dst + BitVec.ofNat 64 (8 * 0) = dst from BitVec.add_zero dst] at h
    exact h
  have h1 : prefixStore m dst w 16 = memStore (prefixStore m dst w 8) (dst + 8) w[1] :=
    prefixStore_word m dst w 1 (by decide)
  have h2 : prefixStore m dst w 24 = memStore (prefixStore m dst w 16) (dst + 16) w[2] :=
    prefixStore_word m dst w 2 (by decide)
  have h3 : prefixStore m dst w 32 = memStore (prefixStore m dst w 24) (dst + 24) w[3] :=
    prefixStore_word m dst w 3 (by decide)
  rw [h3, h2, h1, h0]
  exact storeWords_wordsAt m dst w low

end K256.Proofs.Verify.Core.Serializer
