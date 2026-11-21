import Standards.NIST.SHA3
import Init.Data.BitVec.Lemmas
import Init.Data.Range.Lemmas

namespace Sha3.Proofs.Keccak

open Standards.NIST.SHA3

abbrev Lanes := Fin 25 → BitVec 64

def laneIndex (x y : Fin 5) : Fin 25 := ⟨x.val + 5 * y.val, by omega⟩

def laneX (i : Fin 25) : Fin 5 := ⟨i.val % 5, by omega⟩

def laneY (i : Fin 25) : Fin 5 := ⟨i.val / 5, by omega⟩

theorem laneX_laneIndex (x y : Fin 5) : laneX (laneIndex x y) = x := by
  apply Fin.ext
  simp [laneX, laneIndex, Nat.add_mod, Nat.mod_eq_of_lt x.isLt]

theorem laneY_laneIndex (x y : Fin 5) : laneY (laneIndex x y) = y := by
  apply Fin.ext
  simp only [laneY, laneIndex]
  omega

theorem laneIndex_laneXY (i : Fin 25) : laneIndex (laneX i) (laneY i) = i := by
  apply Fin.ext
  simp only [laneIndex, laneX, laneY]
  omega

def packLane (f : Fin 64 → Bool) : BitVec 64 :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem getLsbD_packLane (f : Fin 64 → Bool) (z : Fin 64) :
    (packLane f).getLsbD z.val = f z := by
  simp only [packLane, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, z.isLt, dite_true, Option.getD_some]

def stateOfLanes (a : Lanes) : StateArray 6 where
  bits := Vector.ofFn fun x ↦ Vector.ofFn fun y ↦ Vector.ofFn fun z ↦
    (a (laneIndex x y)).getLsbD z.val

def lanesOfState (a : StateArray 6) : Lanes := fun i ↦
  packLane fun z ↦ a.bits[(laneX i).val][(laneY i).val][z.val]

theorem state_ext {a b : StateArray 6}
    (h : ∀ x y : Fin 5, ∀ z : Fin 64,
      a.bits[x.val][y.val][z.val] = b.bits[x.val][y.val][z.val]) : a = b := by
  cases a with | mk a =>
    cases b with | mk b =>
      congr 1
      apply Vector.ext
      intro x hx
      apply Vector.ext
      intro y hy
      apply Vector.ext
      intro z hz
      exact h ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩

theorem get_stateOfLanes (a : Lanes) (x y : Fin 5) (z : Fin 64) :
    (stateOfLanes a).bits[x.val][y.val][z.val] =
      (a (laneIndex x y)).getLsbD z.val := by
  simp [stateOfLanes]

theorem get_lanesOfState (a : StateArray 6) (x y : Fin 5) (z : Fin 64) :
    (lanesOfState a (laneIndex x y)).getLsbD z.val = a.bits[x.val][y.val][z.val] := by
  simp only [lanesOfState, getLsbD_packLane, laneX_laneIndex, laneY_laneIndex]

theorem stateOfLanes_lanesOfState (a : StateArray 6) :
    stateOfLanes (lanesOfState a) = a := by
  apply state_ext
  intro x y z
  rw [get_stateOfLanes, get_lanesOfState]

theorem lanesOfState_stateOfLanes (a : Lanes) : lanesOfState (stateOfLanes a) = a := by
  funext i
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro z hz
  simp only [lanesOfState, getLsbD_packLane _ ⟨z, hz⟩, get_stateOfLanes,
    laneIndex_laneXY]

theorem getLsbD_rotateLeft (a : BitVec 64) (r : Nat) (z : Fin 64) :
    (a.rotateLeft r).getLsbD z.val =
      a.getLsbD (z - Fin.ofNat 64 r).val := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [Fin.val_sub, Fin.val_ofNat]
  split
  · congr 1
    omega
  · simp only [z.isLt, decide_true, Bool.true_and]
    congr 1
    omega

def columnParity (a : Lanes) (x : Fin 5) : BitVec 64 :=
  a (laneIndex x 0) ^^^ a (laneIndex x 1) ^^^ a (laneIndex x 2) ^^^
    a (laneIndex x 3) ^^^ a (laneIndex x 4)

def theta (a : Lanes) : Lanes := fun i ↦
  a i ^^^ (columnParity a (laneX i - 1) ^^^ (columnParity a (laneX i + 1)).rotateLeft 1)

def pi (a : Lanes) : Lanes := fun i ↦
  a (laneIndex (laneX i + 3 * laneY i) (laneX i))

def chi (a : Lanes) : Lanes := fun i ↦
  a i ^^^ (~~~ a (laneIndex (laneX i + 1) (laneY i)) &&&
    a (laneIndex (laneX i + 2) (laneY i)))

theorem stateOfLanes_theta (a : Lanes) : stateOfLanes (theta a) = θ (stateOfLanes a) := by
  apply state_ext
  intro x y z
  simp only [stateOfLanes, theta, θ, columnParity, laneX_laneIndex,
    BitVec.getLsbD_xor, getLsbD_rotateLeft _ _ z,
    StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta]
  rfl

theorem stateOfLanes_pi (a : Lanes) : stateOfLanes (pi a) = π (stateOfLanes a) := by
  apply state_ext
  intro x y z
  simp [stateOfLanes, pi, π, laneX_laneIndex, laneY_laneIndex,
    StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW]

theorem stateOfLanes_chi (a : Lanes) : stateOfLanes (chi a) = χ (stateOfLanes a) := by
  apply state_ext
  intro x y z
  simp [stateOfLanes, chi, χ, laneX_laneIndex, laneY_laneIndex,
    StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW, z.isLt]

def setLane (a : Lanes) (i : Fin 25) (v : BitVec 64) : Lanes :=
  fun j ↦ if j = i then v else a j

theorem laneIndex_inj (x y u v : Fin 5) :
    laneIndex x y = laneIndex u v ↔ x = u ∧ y = v := by
  constructor
  · intro h
    exact ⟨by simpa only [laneX_laneIndex] using congrArg laneX h,
      by simpa only [laneY_laneIndex] using congrArg laneY h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem stateOfLanes_setLane (a : Lanes) (x y : Fin 5) (v : BitVec 64) :
    (stateOfLanes (setLane a (laneIndex x y) v)).bits =
      (stateOfLanes a).bits.set x.val
        ((stateOfLanes a).bits[x.val].set y.val (Vector.ofFn fun z ↦ v.getLsbD z.val)) := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro q hq
  apply Vector.ext
  intro z hz
  rw [get_stateOfLanes _ ⟨u, hu⟩ ⟨q, hq⟩ ⟨z, hz⟩]
  simp only [setLane]
  simp only [laneIndex_inj]
  simp only [Fin.ext_iff]
  by_cases hx : x.val = u <;> by_cases hy : y.val = q
  all_goals simp only [eq_comm (a := u), eq_comm (a := q), hx, hy,
    and_self, and_true, and_false, ite_true, ite_false,
    Vector.getElem_set, Vector.getElem_ofFn]
  all_goals exact (get_stateOfLanes a ⟨u, hu⟩ ⟨q, hq⟩ ⟨z, hz⟩).symm

def rhoStep (a : Lanes) (s : Lanes × Fin 5 × Fin 5) (t : Nat) : Lanes × Fin 5 × Fin 5 :=
  (setLane s.1 (laneIndex s.2.1 s.2.2)
    ((a (laneIndex s.2.1 s.2.2)).rotateLeft ((t + 1) * (t + 2) / 2)),
    s.2.2, 2 * s.2.1 + 3 * s.2.2)

def rho (a : Lanes) : Lanes := ((List.range 24).foldl (rhoStep a) (a, 1, 0)).1

theorem stateOfLanes_rho (a : Lanes) : stateOfLanes (rho a) = ρ (stateOfLanes a) := by
  let _ : NeZero (w 6) := ⟨by decide⟩
  unfold ρ
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, Id.run_pure]
  have hRange : List.range' 0 ([:24] : Std.Legacy.Range).size = List.range 24 := by
    decide +kernel
  rw [hRange]
  simp only [rho]
  generalize List.range 24 = ts
  let f : Lanes × Fin 5 × Fin 5 →
      Vector (Vector (Vector Bool (w 6)) 5) 5 × Fin 5 × Fin 5 :=
    fun s ↦ ((stateOfLanes s.1).bits, s.2)
  apply congrArg (StateArray.mk (ℓ := 6))
  change (f (ts.foldl (rhoStep a) (a, 1, 0))).1 = _
  symm
  congr 1
  apply List.foldl_hom f (g₁ := rhoStep a) (l := ts) (init := (a, 1, 0))
  intro s t
  simp only [f, rhoStep, stateOfLanes_setLane]
  have hl : (Vector.ofFn fun z : Fin (w 6) ↦
      (stateOfLanes a)[(s.2.1.val, s.2.2.val,
        (z - Fin.ofNat (w 6) ((t + 1) * (t + 2) / 2)).val)]) =
      Vector.ofFn (fun z : Fin (w 6) ↦
        ((a (laneIndex s.2.1 s.2.2)).rotateLeft ((t + 1) * (t + 2) / 2)).getLsbD z.val) := by
    apply Vector.ext
    intro z hz
    simp only [Vector.getElem_ofFn, StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW,
      getLsbD_rotateLeft _ _ ⟨z, hz⟩]
    exact get_stateOfLanes a s.2.1 s.2.2
      (⟨z, hz⟩ - Fin.ofNat 64 ((t + 1) * (t + 2) / 2))
  rw [hl]
  rfl

def roundConstantBits (ir : Int) : Vector Bool (w 6) := Id.run do
  let mut c := Vector.replicate (w 6) false
  for hj : j in [:7] do
    c := c.set (2 ^ j - 1) (rc (j + 7 * ir)) (by
      have hjlt : j < 7 := hj.2.1
      have hpow : 2 ^ j ≤ w 6 := Nat.pow_le_pow_right (by decide) (by omega)
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
      omega)
  return c

def roundConstant (ir : Int) : BitVec 64 :=
  packLane fun z ↦ (roundConstantBits ir)[z.val]

def iota (a : Lanes) (ir : Int) : Lanes :=
  setLane a (laneIndex 0 0) (a (laneIndex 0 0) ^^^ roundConstant ir)

theorem stateOfLanes_iota (a : Lanes) (ir : Int) :
    stateOfLanes (iota a ir) = ι (stateOfLanes a) ir := by
  unfold ι
  change stateOfLanes (iota a ir) =
    ⟨(stateOfLanes a).bits.set 0 ((stateOfLanes a).bits[0].set 0
      (Vector.ofFn fun z ↦ (stateOfLanes a)[(0, 0, z.val)] ^^ (roundConstantBits ir)[z]))⟩
  apply congrArg (StateArray.mk (ℓ := 6))
  change (stateOfLanes (setLane a (laneIndex 0 0)
    (a (laneIndex 0 0) ^^^ roundConstant ir))).bits = _
  rw [stateOfLanes_setLane]
  have hl : (Vector.ofFn fun z : Fin (w 6) ↦
      (a (laneIndex 0 0) ^^^ roundConstant ir).getLsbD z.val) =
      Vector.ofFn (fun z : Fin (w 6) ↦
        (stateOfLanes a)[(0, 0, z.val)] ^^ (roundConstantBits ir)[z]) := by
    apply Vector.ext
    intro z hz
    simp only [Vector.getElem_ofFn, StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW,
      BitVec.getLsbD_xor, roundConstant, getLsbD_packLane _ ⟨z, hz⟩, Fin.getElem_fin]
    exact congrArg (fun bit ↦ bit ^^ (roundConstantBits ir)[z])
      (get_stateOfLanes a 0 0 ⟨z, hz⟩).symm
  rw [hl]
  rfl

def roundLanes (a : Lanes) (ir : Int) : Lanes :=
  iota (chi (pi (rho (theta a)))) ir

theorem stateOfLanes_roundLanes (a : Lanes) (ir : Int) :
    stateOfLanes (roundLanes a ir) = Standards.NIST.SHA3.round (stateOfLanes a) ir := by
  simp only [roundLanes, Standards.NIST.SHA3.round, stateOfLanes_iota, stateOfLanes_chi,
    stateOfLanes_pi, stateOfLanes_rho, stateOfLanes_theta]

def keccakLanes (a : Lanes) : Lanes :=
  (List.range 24).foldl (fun a (i : Nat) ↦ roundLanes a (i : Int)) a

theorem ofString_toString (a : StateArray 6) : StateArray.ofString a.toString = a := by
  apply state_ext
  intro x y z
  simp only [StateArray.ofString, StateArray.toString, Vector.getElem_ofFn,
    StateArray.instGetElemProdNatBoolAndLtFstOfNatSndW]
  have hx : ((w 6 * (5 * y.val + x.val) + z.val) / w 6) % 5 = x.val := by
    change ((64 * (5 * y.val + x.val) + z.val) / 64) % 5 = x.val
    omega
  have hy : ((w 6 * (5 * y.val + x.val) + z.val) / w 6) / 5 = y.val := by
    change ((64 * (5 * y.val + x.val) + z.val) / 64) / 5 = y.val
    omega
  have hz : (w 6 * (5 * y.val + x.val) + z.val) % w 6 = z.val := by
    change (64 * (5 * y.val + x.val) + z.val) % 64 = z.val
    omega
  simp only [hx, hy, hz]

theorem stateOfLanes_keccakLanes (a : Lanes) :
    (stateOfLanes (keccakLanes a)).toString =
      keccakF 6 (stateOfLanes a).toString := by
  unfold keccakF keccakP
  simp only [ofString_toString, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  change (stateOfLanes (keccakLanes a)).toString =
    ((List.range' 0 ([:24] : Std.Legacy.Range).size).foldl
      (fun a (i : Nat) ↦ Standards.NIST.SHA3.round a (0 + (i : Int))) (stateOfLanes a)).toString
  have hRange : List.range' 0 ([:24] : Std.Legacy.Range).size = List.range 24 := by
    decide +kernel
  rw [hRange]
  simp only [Int.zero_add, keccakLanes]
  apply congrArg StateArray.toString
  symm
  exact List.foldl_hom stateOfLanes
    (g₁ := fun a (i : Nat) ↦ roundLanes a (i : Int))
    (fun a i ↦ (stateOfLanes_roundLanes a (i : Int)).symm)

def rhoOffsets : Vector Nat 25 :=
  #v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
    41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

private def rhoOffsetStep (s : (Fin 25 → Nat) × Fin 5 × Fin 5) (t : Nat) :
    (Fin 25 → Nat) × Fin 5 × Fin 5 :=
  ((fun i ↦ if i = laneIndex s.2.1 s.2.2 then (t + 1) * (t + 2) / 2 else s.1 i),
    s.2.2, 2 * s.2.1 + 3 * s.2.2)

theorem rho_apply (a : Lanes) (i : Fin 25) :
    rho a i = (a i).rotateLeft rhoOffsets[i.val] := by
  let f : (Fin 25 → Nat) × Fin 5 × Fin 5 → Lanes × Fin 5 × Fin 5 :=
    fun s ↦ ((fun j ↦ (a j).rotateLeft (s.1 j)), s.2)
  have h := List.foldl_hom f (g₁ := rhoOffsetStep) (g₂ := rhoStep a)
    (l := List.range 24) (init := ((fun _ ↦ 0), 1, 0)) (by
      intro s t
      apply Prod.ext
      · funext j
        simp only [rhoStep, f, setLane, rhoOffsetStep]
        by_cases hj : j = laneIndex s.2.1 s.2.2
        · simp [hj]
        · simp [hj]
      · rfl)
  have hinit : f ((fun _ ↦ 0), 1, 0) = (a, 1, 0) := by
    have hzero (v : BitVec 64) : v.rotateLeft 0 = v := by
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro z hz
      simp only [BitVec.getLsbD_rotateLeft, Nat.zero_mod, Nat.not_lt_zero, ite_false,
        hz, decide_true, Bool.true_and, Nat.sub_zero]
    simp only [f, hzero]
  rw [hinit] at h
  have hoff : ∀ j : Fin 25,
      ((List.range 24).foldl rhoOffsetStep ((fun _ ↦ 0), 1, 0)).1 j % 64 =
        rhoOffsets[j.val] := by
    decide +kernel
  have hi := congrArg (fun s : Lanes × Fin 5 × Fin 5 ↦ s.1 i) h
  dsimp only [f] at hi
  simp only [rho]
  rw [hi, ← BitVec.rotateLeft_mod_eq_rotateLeft, hoff i]

def roundConstants : Vector (BitVec 64) 24 :=
  #v[0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

theorem roundConstant_eq (ir : Fin 24) :
    roundConstant (ir.val : Int) = roundConstants[ir.val] := by
  have h : ∀ i : Fin 24, roundConstant (i.val : Int) = roundConstants[i.val] := by
    decide +kernel
  exact h ir

end Sha3.Proofs.Keccak
