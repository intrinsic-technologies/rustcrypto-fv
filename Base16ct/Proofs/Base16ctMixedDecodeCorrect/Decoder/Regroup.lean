import Standards.RFC.BaseEncodings.Decoding

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

open Standards.RFC.BaseEncodings

def pairOctets : List Nat → List UInt8
  | [] => []
  | [_] => []
  | a :: b :: rest => UInt8.ofNat (16 * a + b) :: pairOctets rest

private theorem nibble_testBits (n : Nat) (hn : n < 16) :
    2 * (2 * (2 * (n.testBit 3).toNat + (n.testBit 2).toNat) +
      (n.testBit 1).toNat) + (n.testBit 0).toNat = n := by
  have h : ∀ n : Fin 16,
      2 * (2 * (2 * (n.val.testBit 3).toNat + (n.val.testBit 2).toNat) +
        (n.val.testBit 1).toNat) + (n.val.testBit 0).toNat = n.val := by
    decide +kernel
  exact h ⟨n, hn⟩

private theorem ofBits_pair (a b : Nat) (rest : List Nat) (ha : a < 16) (hb : b < 16) :
    ofBits 8 (fun j ↦ streamBit 4 (a :: b :: rest) j) = 16 * a + b := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [ofBits, h8, List.foldl_cons, List.foldl_nil, streamBit,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, List.getD_cons_zero,
    List.getD_cons_succ, Nat.mul_zero, Nat.zero_add]
  have ha' := nibble_testBits a ha
  have hb' := nibble_testBits b hb
  omega

private theorem streamBit_pair_tail (a b : Nat) (rest : List Nat) (k : Nat) :
    streamBit 4 (a :: b :: rest) (8 + k) = streamBit 4 rest k := by
  have hd : (8 + k) / 4 = k / 4 + 1 + 1 := by omega
  have hm : (8 + k) % 4 = k % 4 := by omega
  simp only [streamBit, hd, hm, List.getD_cons_succ]

private theorem regroup_pair (a b : Nat) (rest : List Nat) (count : Nat)
    (ha : a < 16) (hb : b < 16) :
    regroup 4 8 (a :: b :: rest) (count + 1) =
      (16 * a + b) :: regroup 4 8 rest count := by
  simp only [regroup, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.mul_zero, Nat.zero_add, ofBits_pair a b rest ha hb]
  congr 1
  apply List.map_congr_left
  intro i _
  change ofBits 8 (fun j ↦ streamBit 4 (a :: b :: rest) (8 * (i + 1) + j)) =
    ofBits 8 (fun j ↦ streamBit 4 rest (8 * i + j))
  apply congrArg (ofBits 8)
  funext j
  rw [show 8 * (i + 1) + j = 8 + (8 * i + j) by omega, streamBit_pair_tail]

private theorem regroup_pairOctets (values : List Nat) (h : ∀ v ∈ values, v < 16) :
    (regroup 4 8 values (values.length / 2)).map UInt8.ofNat = pairOctets values := by
  match values with
  | [] => rfl
  | [a] => simp [regroup, pairOctets]
  | a :: b :: rest =>
    have ha : a < 16 := h a (by simp)
    have hb : b < 16 := h b (by simp)
    have hr : ∀ v ∈ rest, v < 16 := fun v hv ↦ h v (by simp [hv])
    have hc : (a :: b :: rest).length / 2 = rest.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    rw [hc, regroup_pair a b rest _ ha hb]
    simp only [List.map_cons, pairOctets]
    exact congrArg (UInt8.ofNat (16 * a + b) :: ·) (regroup_pairOctets rest hr)

theorem octetsOf_base16Upper (values : List Nat) (h : ∀ v ∈ values, v < 16) :
    (octetsOf .base16Upper values).data.toList = pairOctets values := by
  change ((regroup 4 8 values (4 * values.length / 8)).map UInt8.ofNat).toArray.toList = _
  rw [List.toList_toArray, show 4 * values.length / 8 = values.length / 2 by omega]
  exact regroup_pairOctets values h

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
