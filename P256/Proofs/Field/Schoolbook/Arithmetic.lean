import P256.Proofs.Field.Schoolbook.Carry

set_option autoImplicit false

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)

def firstRow (p0 p1 p2 p3 : Nat) : Vector Nat 5 :=
  let r1 := addWord (p0 / wordBase) (p1 % wordBase) 0
  let r2 := addWord (p2 % wordBase) (p1 / wordBase) r1.2
  let r3 := addWord (p3 % wordBase) (p2 / wordBase) r2.2
  #v[p0 % wordBase, r1.1, r2.1, r3.1, p3 / wordBase + r3.2]

def packFive (v : Vector Nat 5) : Nat :=
  v[0] + wordBase*v[1] + wordBase^2*v[2] + wordBase^3*v[3] + wordBase^4*v[4]

theorem packFive_firstRow (p0 p1 p2 p3 : Nat) :
    packFive (firstRow p0 p1 p2 p3) =
      p0 + wordBase*p1 + wordBase^2*p2 + wordBase^3*p3 := by
  dsimp [packFive, firstRow, addWord, wordBase]
  omega

theorem firstRow_lt (p0 p1 p2 p3 : Nat)
    (h0 : p0 ≤ (wordBase-1)*(wordBase-1))
    (h1 : p1 ≤ (wordBase-1)*(wordBase-1))
    (h2 : p2 ≤ (wordBase-1)*(wordBase-1))
    (h3 : p3 ≤ (wordBase-1)*(wordBase-1)) (i : Nat) (hi : i < 5) :
    (firstRow p0 p1 p2 p3)[i] < wordBase := by
  have hidx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hidx with rfl | rfl | rfl | rfl | rfl
  all_goals dsimp [firstRow, addWord, wordBase] at *
  all_goals omega

def secondRow (r : Vector Nat 5) (p0 p1 p2 p3 : Nat) : Vector Nat 6 :=
  let v1 := addWord r[1] (p0 % wordBase) 0
  let v2 := addProduct p1 (p0 / wordBase + v1.2) r[2]
  let v3 := addProduct p2 v2.2 r[3]
  let v4 := addProduct p3 v3.2 r[4]
  #v[r[0], v1.1, v2.1, v3.1, v4.1, v4.2]

def packSix (v : Vector Nat 6) : Nat :=
  v[0] + wordBase*v[1] + wordBase^2*v[2] + wordBase^3*v[3] +
    wordBase^4*v[4] + wordBase^5*v[5]

theorem packSix_secondRow (r : Vector Nat 5) (p0 p1 p2 p3 : Nat)
    (hr : ∀ i : Fin 5, r[i] < wordBase)
    (h0 : p0 ≤ (wordBase-1)*(wordBase-1))
    (h1 : p1 ≤ (wordBase-1)*(wordBase-1))
    (h2 : p2 ≤ (wordBase-1)*(wordBase-1))
    (h3 : p3 ≤ (wordBase-1)*(wordBase-1)) :
    packSix (secondRow r p0 p1 p2 p3) =
      packFive r + wordBase * (p0 + wordBase*p1 + wordBase^2*p2 + wordBase^3*p3) := by
  let v1 := addWord r[1] (p0 % wordBase) 0
  let v2 := addProduct p1 (p0 / wordBase + v1.2) r[2]
  let v3 := addProduct p2 v2.2 r[3]
  let v4 := addProduct p3 v3.2 r[4]
  have hv1 : v1.1 + wordBase*v1.2 = r[1] + p0%wordBase := by
    simpa only [Nat.add_zero] using addWord_eq r[1] (p0%wordBase) 0
  have hcarry : p0 / wordBase + v1.2 < wordBase := by
    have hc := addWord_high_le_one (hr 1) (Nat.mod_lt p0 (by decide)) (Nat.zero_le 1)
    change v1.2 ≤ 1 at hc
    dsimp only [wordBase] at *
    omega
  have hv2 := addProduct_eq h1 hcarry (hr 2)
  have hv3 := addProduct_eq h2 (addProduct_high_lt p1 (p0/wordBase+v1.2) r[2]) (hr 3)
  have hv4 := addProduct_eq h3 (addProduct_high_lt p2 v2.2 r[3]) (hr 4)
  change v2.1 + wordBase*v2.2 = p1 + (p0/wordBase+v1.2) + r[2] at hv2
  change v3.1 + wordBase*v3.2 = p2 + v2.2 + r[3] at hv3
  change v4.1 + wordBase*v4.2 = p3 + v3.2 + r[4] at hv4
  change r[0] + wordBase*v1.1 + wordBase^2*v2.1 + wordBase^3*v3.1 +
    wordBase^4*v4.1 + wordBase^5*v4.2 = _
  change r[0] + wordBase*v1.1 + wordBase^2*v2.1 + wordBase^3*v3.1 +
    wordBase^4*v4.1 + wordBase^5*v4.2 =
    r[0] + wordBase*r[1] + wordBase^2*r[2] + wordBase^3*r[3] + wordBase^4*r[4] +
    wordBase * (p0 + wordBase*p1 + wordBase^2*p2 + wordBase^3*p3)
  dsimp only [wordBase] at *
  omega

def lastRows (r : Vector Nat 6) (q p : Vector Nat 4) : Vector Nat 8 :=
  let v2 := addWord (q[0] % wordBase) r[2] 0
  let q1 := addProduct q[1] (q[0] / wordBase + v2.2) r[3]
  let v3 := addWord q1.1 (p[0] % wordBase) 0
  let q2 := addProduct q[2] q1.2 r[4]
  let p1 := addProduct p[1] (p[0] / wordBase + v3.2) q2.1
  let q3 := addProduct q[3] q2.2 r[5]
  let p2 := addProduct p[2] p1.2 q3.1
  let p3 := addProduct p[3] p2.2 q3.2
  #v[r[0], r[1], v2.1, v3.1, p1.1, p2.1, p3.1, p3.2]

def packEight (v : Vector Nat 8) : Nat :=
  v[0] + wordBase*v[1] + wordBase^2*v[2] + wordBase^3*v[3] +
    wordBase^4*v[4] + wordBase^5*v[5] + wordBase^6*v[6] + wordBase^7*v[7]

theorem packEight_lastRows (r : Vector Nat 6) (q p : Vector Nat 4)
    (hr : ∀ i : Fin 6, r[i] < wordBase)
    (hq : ∀ i : Fin 4, q[i] ≤ (wordBase-1)*(wordBase-1))
    (hp : ∀ i : Fin 4, p[i] ≤ (wordBase-1)*(wordBase-1)) :
    packEight (lastRows r q p) = packSix r +
      wordBase^2 * (q[0] + wordBase*q[1] + wordBase^2*q[2] + wordBase^3*q[3]) +
      wordBase^3 * (p[0] + wordBase*p[1] + wordBase^2*p[2] + wordBase^3*p[3]) := by
  let v2 := addWord (q[0] % wordBase) r[2] 0
  let q1 := addProduct q[1] (q[0] / wordBase + v2.2) r[3]
  let v3 := addWord q1.1 (p[0] % wordBase) 0
  let q2 := addProduct q[2] q1.2 r[4]
  let p1 := addProduct p[1] (p[0] / wordBase + v3.2) q2.1
  let q3 := addProduct q[3] q2.2 r[5]
  let p2 := addProduct p[2] p1.2 q3.1
  let p3 := addProduct p[3] p2.2 q3.2
  have hv2 : v2.1 + wordBase*v2.2 = q[0]%wordBase + r[2] := by
    simpa only [Nat.add_zero] using addWord_eq (q[0]%wordBase) r[2] 0
  have hqc : q[0]/wordBase + v2.2 < wordBase := by
    have hc := addWord_high_le_one (Nat.mod_lt q[0] (by decide)) (hr 2) (Nat.zero_le 1)
    change v2.2 ≤ 1 at hc
    have hq0 := hq 0
    change q[0] ≤ (wordBase-1)*(wordBase-1) at hq0
    dsimp only [wordBase] at *
    omega
  have hq1 := addProduct_eq (hq 1) hqc (hr 3)
  change q1.1 + wordBase*q1.2 = q[1] + (q[0]/wordBase+v2.2) + r[3] at hq1
  have hv3 : v3.1 + wordBase*v3.2 = q1.1 + p[0]%wordBase := by
    simpa only [Nat.add_zero] using addWord_eq q1.1 (p[0]%wordBase) 0
  have hpc : p[0]/wordBase + v3.2 < wordBase := by
    have hc := addWord_high_le_one (addProduct_low_lt q[1] (q[0]/wordBase+v2.2) r[3])
      (Nat.mod_lt p[0] (by decide)) (Nat.zero_le 1)
    change v3.2 ≤ 1 at hc
    have hp0 := hp 0
    change p[0] ≤ (wordBase-1)*(wordBase-1) at hp0
    dsimp only [wordBase] at *
    omega
  have hq2 := addProduct_eq (hq 2) (addProduct_high_lt q[1] (q[0]/wordBase+v2.2) r[3]) (hr 4)
  change q2.1 + wordBase*q2.2 = q[2] + q1.2 + r[4] at hq2
  have hp1 := addProduct_eq (hp 1) hpc (addProduct_low_lt q[2] q1.2 r[4])
  change p1.1 + wordBase*p1.2 = p[1] + (p[0]/wordBase+v3.2) + q2.1 at hp1
  have hq3 := addProduct_eq (hq 3) (addProduct_high_lt q[2] q1.2 r[4]) (hr 5)
  change q3.1 + wordBase*q3.2 = q[3] + q2.2 + r[5] at hq3
  have hp2 := addProduct_eq (hp 2) (addProduct_high_lt p[1] (p[0]/wordBase+v3.2) q2.1) (addProduct_low_lt q[3] q2.2 r[5])
  change p2.1 + wordBase*p2.2 = p[2] + p1.2 + q3.1 at hp2
  have hp3 := addProduct_eq (hp 3) (addProduct_high_lt p[2] p1.2 q3.1) (addProduct_high_lt q[3] q2.2 r[5])
  change p3.1 + wordBase*p3.2 = p[3] + p2.2 + q3.2 at hp3
  change r[0] + wordBase*r[1] + wordBase^2*v2.1 + wordBase^3*v3.1 +
    wordBase^4*p1.1 + wordBase^5*p2.1 + wordBase^6*p3.1 + wordBase^7*p3.2 =
    r[0] + wordBase*r[1] + wordBase^2*r[2] + wordBase^3*r[3] +
    wordBase^4*r[4] + wordBase^5*r[5] +
      wordBase^2 * (q[0] + wordBase*q[1] + wordBase^2*q[2] + wordBase^3*q[3]) +
      wordBase^3 * (p[0] + wordBase*p[1] + wordBase^2*p[2] + wordBase^3*p[3])
  dsimp only [wordBase] at *
  omega

theorem secondRow_lt (r : Vector Nat 5) (p0 p1 p2 p3 : Nat)
    (h0 : r[0] < wordBase) (i : Nat) (hi : i < 6) :
    (secondRow r p0 p1 p2 p3)[i] < wordBase := by
  have hidx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hidx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact addWord_low_lt _ _ _
  · exact addProduct_low_lt _ _ _
  · exact addProduct_low_lt _ _ _
  · exact addProduct_low_lt _ _ _
  · exact addProduct_high_lt _ _ _

def schoolbookLimbs (a b : Vector Nat 4) : Vector Nat 8 :=
  let first := firstRow (a[0]*b[0]) (a[0]*b[1]) (a[0]*b[2]) (a[0]*b[3])
  let second := secondRow first (a[1]*b[0]) (a[1]*b[1]) (a[1]*b[2]) (a[1]*b[3])
  lastRows second (b.map (a[2]*·)) (b.map (a[3]*·))

def packFour (v : Vector Nat 4) : Nat :=
  v[0] + wordBase*v[1] + wordBase^2*v[2] + wordBase^3*v[3]

theorem schoolbookLimbs_correct (a b : Vector Nat 4)
    (ha : ∀ i : Fin 4, a[i] < wordBase) (hb : ∀ i : Fin 4, b[i] < wordBase) :
    packEight (schoolbookLimbs a b) = packFour a * packFour b := by
  have hp (i j : Fin 4) : a[i]*b[j] ≤ (wordBase-1)*(wordBase-1) :=
    mulWord_bound (ha i) (hb j)
  let first := firstRow (a[0]*b[0]) (a[0]*b[1]) (a[0]*b[2]) (a[0]*b[3])
  let second := secondRow first (a[1]*b[0]) (a[1]*b[1]) (a[1]*b[2]) (a[1]*b[3])
  have hf : ∀ i : Fin 5, first[i] < wordBase := fun i =>
    firstRow_lt _ _ _ _ (hp 0 0) (hp 0 1) (hp 0 2) (hp 0 3) i.val i.isLt
  have hs : ∀ i : Fin 6, second[i] < wordBase := fun i =>
    secondRow_lt _ _ _ _ _ (hf 0) i.val i.isLt
  have hq : ∀ i : Fin 4, (b.map (a[2]*·))[i] ≤ (wordBase-1)*(wordBase-1) := by
    intro i
    change (b.map (a[2]*·))[i.val] ≤ _
    rw [Vector.getElem_map]
    exact hp 2 i
  have hr : ∀ i : Fin 4, (b.map (a[3]*·))[i] ≤ (wordBase-1)*(wordBase-1) := by
    intro i
    change (b.map (a[3]*·))[i.val] ≤ _
    rw [Vector.getElem_map]
    exact hp 3 i
  change packEight (lastRows second (b.map (a[2]*·)) (b.map (a[3]*·))) = _
  rw [packEight_lastRows second _ _ hs hq hr]
  rw [show packSix second = packFive first + wordBase *
      (a[1]*b[0] + wordBase*(a[1]*b[1]) + wordBase^2*(a[1]*b[2]) +
        wordBase^3*(a[1]*b[3])) from
      packSix_secondRow first _ _ _ _ hf (hp 1 0) (hp 1 1) (hp 1 2) (hp 1 3)]
  rw [show packFive first = a[0]*b[0] + wordBase*(a[0]*b[1]) +
      wordBase^2*(a[0]*b[2]) + wordBase^3*(a[0]*b[3]) from packFive_firstRow _ _ _ _]
  simp only [packFour, Vector.getElem_map]
  grind only

end P256.Proofs.Field.Schoolbook
