import K256.Proofs.Common.Point.Segment

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine

inductive Slot where
  | stack (i : Fin 68)
  | left (i : Fin 15)
  | right (i : Fin 15)
  deriving DecidableEq

def Slot.address (fr : Activation) : Slot → BitVec 64
  | .stack i => (fr.rsp - 536) + BitVec.ofNat 64 (8 * i.val)
  | .left i => fr.rdi + BitVec.ofNat 64 (8 * i.val)
  | .right i => fr.rsi + BitVec.ofNat 64 (8 * i.val)

structure Bounds (fr : Activation) : Prop where
  room : 536 ≤ fr.rsp.toNat
  srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat
  dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  srcLow : fr.rsi.toNat + 120 ≤ 2^32
  dstLow : fr.rdi.toNat + 120 ≤ 2^32
  apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat

private theorem offsetNat (a : BitVec 64) (i : Nat) (h : a.toNat + 8 * i < 2^64) :
    (a + BitVec.ofNat 64 (8 * i)).toNat = a.toNat + 8 * i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * i < 2^64 by omega),
    Nat.mod_eq_of_lt h]

theorem Slot.apart {fr : Activation} (h : Bounds fr) {i j : Slot} (ne : i ≠ j) :
    RangeApart (i.address fr) 8 (j.address fr) 8 := by
  obtain ⟨room, sa, da, sl, dl, sep⟩ := h
  have sp : (fr.rsp - 536).toNat = fr.rsp.toNat - 536 :=
    BitVec.toNat_sub_of_le room
  cases i <;> cases j <;> rename_i x y <;>
    have hx := x.isLt <;> have hy := y.isLt <;>
    apply RangeApart.of_toNat <;>
    simp (disch := omega) only [Slot.address, offsetNat, sp] <;>
    first | omega | (have diff : x.val ≠ y.val := fun eq => ne (by congr 1; exact Fin.ext eq); omega)

def Matches (fr : Activation) (m : Ram) (words : Slot → BitVec 64) : Prop :=
  ∀ i, memLoad m (i.address fr) 64 = words i

theorem Matches.store {fr : Activation} (h : Bounds fr) {m : Ram} {words : Slot → BitVec 64}
    (initial : Matches fr m words) (i : Slot) (v : BitVec 64) :
    Matches fr (memStore m (i.address fr) v) (fun j => if i = j then v else words j) := by
  intro j
  change _ = if i = j then v else words j
  by_cases eq : i = j
  · subst j
    rw [ite_eq_left (rfl : i = i), memLoad_memStore_same _ _ _ (by decide) (by decide)]
  · rw [ite_eq_right eq, memLoad_memStore_of_rangeApart _ _ _ _ _ (Slot.apart h eq)]
    exact initial j

def Slot.index : Slot → Nat
  | .stack i => i.val
  | .left i => 68 + i.val
  | .right i => 83 + i.val

abbrev Codes := Slot → Nat

def put (codes : Codes) (i : Slot) (k : Nat) : Codes :=
  fun j => if i = j then k else codes j

def Models (fr : Activation) (decode : Nat → BitVec 64) (m : Ram) (codes : Codes) : Prop :=
  Matches fr m (fun j => decode (codes j))

theorem Models.readAt {fr : Activation} {decode : Nat → BitVec 64} {m : Ram} {codes : Codes}
    (initial : Models fr decode m codes) (i : Slot) {a : BitVec 64} (eq : a = i.address fr) :
    memLoad m a 64 = decode (codes i) :=
  eq ▸ initial i

theorem Models.writeAt {fr : Activation} (h : Bounds fr) {decode : Nat → BitVec 64}
    {m : Ram} {codes : Codes} (initial : Models fr decode m codes) (i : Slot) (k : Nat)
    {a v : BitVec 64} (addr : a = i.address fr) (value : v = decode k) :
    Models fr decode (memStore m a v) (put codes i k) := by
  subst a v
  intro j
  simpa only [put, apply_ite decode] using Matches.store h initial i (decode k) j

theorem Models.changeCodes {fr : Activation} {decode : Nat → BitVec 64} {m : Ram} {x y : Codes}
    (hx : Models fr decode m x) (stack : ∀ i, x (.stack i) = y (.stack i))
    (left : ∀ i, x (.left i) = y (.left i)) (right : ∀ i, x (.right i) = y (.right i)) :
    Models fr decode m y := by
  intro j
  exact (hx j).trans (congrArg decode (by cases j <;> first | apply stack | apply left | apply right))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
