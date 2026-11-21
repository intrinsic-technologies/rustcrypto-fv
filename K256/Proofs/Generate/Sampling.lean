import K256.Proofs.Generate.Sampling.Predicate

namespace K256.Proofs.Generate.Sampling

open K256.Proofs.Common K256.Spec Prelude
open Standards.SECG.ECC Standards.SECG.DomainParameters X86.Machine

def decodeBlock (random : ByteArray) (block : Nat) : Option Nat :=
  Keys.decodeSecret Secp256k1.domain (random.extract (32 * block) (32 * block + 32))

theorem decodeBlock_eq {mem : Ram} {region : MemoryRegion} {random : ByteArray}
    (hBytes : region.HasBytes mem random) {block : Nat} (hbound : block < random.size / 32) :
    let w := scalarWord mem (BitVec.ofNat 64 (region.start + 32 * block))
    decodeBlock random block =
      if orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
          ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0)
      then some (limbsValue (w 0) (w 1) (w 2) (w 3))
      else none :=
  decodeSecret_extract_eq hBytes (by omega)

theorem randomSecret_eq_remaining {random : ByteArray} {block : Nat}
    (hbound : block ≤ random.size / 32)
    (hrejected : ∀ i < block, decodeBlock random i = none) :
    Secp256k1.randomSecret random =
      (List.range' block (random.size / 32 - block)).findSome? (decodeBlock random) := by
  have hsplit : List.range (random.size / 32) =
      List.range block ++ List.range' block (random.size / 32 - block) := by
    rw [List.range_eq_range', List.range_eq_range' (n := block)]
    have h := List.range'_append_1 (s := 0) (m := block) (n := random.size / 32 - block)
    rw [Nat.zero_add, Nat.add_sub_of_le hbound] at h
    exact h.symm
  have hnone : (List.range block).findSome? (decodeBlock random) = none := by
    exact List.findSome?_eq_none_iff.mpr (fun i hi => hrejected i (List.mem_range.mp hi))
  change (List.range (random.size / 32)).findSome? (decodeBlock random) = _
  rw [hsplit, List.findSome?_append, hnone]
  rfl

theorem randomSecret_of_accepted {random : ByteArray} {block scalar : Nat}
    (hbound : block < random.size / 32)
    (hrejected : ∀ i < block, decodeBlock random i = none)
    (haccepted : decodeBlock random block = some scalar) :
    Secp256k1.randomSecret random = some scalar := by
  rw [randomSecret_eq_remaining (Nat.le_of_lt hbound) hrejected,
    show random.size / 32 - block = (random.size / 32 - block - 1) + 1 by omega]
  simp only [List.range'_succ, List.findSome?_cons, haccepted]

theorem rejectedPrefix_succ {random : ByteArray} {block : Nat}
    (hrejected : ∀ i < block, decodeBlock random i = none)
    (hnext : decodeBlock random block = none) :
    ∀ i < block + 1, decodeBlock random i = none := by
  intro i hi
  by_cases h : i < block
  · exact hrejected i h
  · rwa [show i = block by omega]

private theorem first_of_findSome_range {α : Type} {f : Nat → Option α}
    {count : Nat} {value : α}
    (h : (List.range count).findSome? f = some value) :
    ∃ i < count, f i = some value ∧ ∀ j < i, f j = none := by
  induction count with
  | zero => simp at h
  | succ count ih =>
    rw [List.range_succ, List.findSome?_append] at h
    cases hp : (List.range count).findSome? f with
    | none =>
      have hv : f count = some value := by
        simpa only [hp, Option.none_or, List.findSome?_singleton] using h
      exact ⟨count, Nat.lt_succ_self count, hv,
        fun j hj => List.findSome?_eq_none_iff.mp hp j (List.mem_range.mpr hj)⟩
    | some earlier =>
      have hv : earlier = value := by
        simpa only [hp, Option.some_or, Option.some.injEq] using h
      subst earlier
      obtain ⟨i, hi, hv, hfirst⟩ := ih hp
      exact ⟨i, Nat.lt_succ_of_lt hi, hv, hfirst⟩

theorem randomSecret_eq_some_iff {random : ByteArray} {scalar : Nat} :
    Secp256k1.randomSecret random = some scalar ↔
      ∃ block < random.size / 32,
        decodeBlock random block = some scalar ∧ ∀ i < block, decodeBlock random i = none := by
  constructor
  · exact first_of_findSome_range
  · rintro ⟨block, hbound, haccepted, hrejected⟩
    exact randomSecret_of_accepted hbound hrejected haccepted

theorem randomSecret_isSome_iff {random : ByteArray} :
    (Secp256k1.randomSecret random).isSome ↔
      ∃ block scalar, block < random.size / 32 ∧
        decodeBlock random block = some scalar ∧ ∀ i < block, decodeBlock random i = none := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨scalar, hs⟩
    obtain ⟨block, hbound, haccepted, hrejected⟩ := randomSecret_eq_some_iff.mp hs
    exact ⟨block, scalar, hbound, haccepted, hrejected⟩
  · rintro ⟨block, scalar, hbound, haccepted, hrejected⟩
    exact ⟨scalar, randomSecret_of_accepted hbound hrejected haccepted⟩

end K256.Proofs.Generate.Sampling
