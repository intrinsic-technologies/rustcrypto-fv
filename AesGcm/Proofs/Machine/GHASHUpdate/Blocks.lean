import AesGcm.Proofs.Machine.GHASHInterface

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.GHASHInterface AesGcm.Proofs.Machine.GHASH

theorem updateBlocks_zero (mem : Ram) (src y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) :
    updateBlocks mem src 0 y0 y1 initial = initial := rfl

theorem updateBlocks_succ (mem : Ram) (src y0 y1 : BitVec 64) (n : Nat)
    (initial : BitVec 64 × BitVec 64) :
    updateBlocks mem src (n + 1) y0 y1 initial =
      let acc := updateBlocks mem src n y0 y1 initial
      polyvalMultiplyWords
        (acc.1 ^^^ bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*n+8)) 64))
        (acc.2 ^^^ bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*n)) 64)) y0 y1 := by
  simp only [updateBlocks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem updateBlocks_append (mem : Ram) (src y0 y1 : BitVec 64) (m n : Nat)
    (initial : BitVec 64 × BitVec 64) :
    updateBlocks mem src (m + n) y0 y1 initial =
      updateBlocks mem (src + BitVec.ofNat 64 (16*m)) n y0 y1
        (updateBlocks mem src m y0 y1 initial) := by
  unfold updateBlocks
  rw [List.range_add, List.foldl_append, List.foldl_map]
  apply congrArg (fun f : (BitVec 64 × BitVec 64) → Nat → (BitVec 64 × BitVec 64) =>
    (List.range n).foldl f (updateBlocks mem src m y0 y1 initial))
  funext acc j
  simp only [Nat.mul_add, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]

theorem foldl_congr_on {α β : Type} (xs : List α) (f g : β → α → β) (initial : β)
    (h : ∀ acc j, j ∈ xs → f acc j = g acc j) : xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.foldl_cons]
    rw [h initial j (List.mem_cons_self)]
    exact ih _ (fun acc k hk => h acc k (List.mem_cons_of_mem _ hk))

theorem updateBlocks_congr (mem mem' : Ram) (src src' y0 y1 : BitVec 64) (n : Nat)
    (initial : BitVec 64 × BitVec 64)
    (h0 : ∀ j < n, memLoad mem (src + BitVec.ofNat 64 (16*j)) 64 =
      memLoad mem' (src' + BitVec.ofNat 64 (16*j)) 64)
    (h1 : ∀ j < n, memLoad mem (src + BitVec.ofNat 64 (16*j+8)) 64 =
      memLoad mem' (src' + BitVec.ofNat 64 (16*j+8)) 64) :
    updateBlocks mem src n y0 y1 initial = updateBlocks mem' src' n y0 y1 initial := by
  unfold updateBlocks
  apply foldl_congr_on
  intro acc j hj
  have hj' := List.mem_range.mp hj
  rw [h0 j hj', h1 j hj']

def rawUpdateBlocks (mem : Ram) (src : BitVec 64) (count : Nat)
    (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range count).foldl (fun acc j => polyvalMultiplyWords
    (memLoad mem (src + BitVec.ofNat 64 (16*j)) 64 ^^^ acc.1)
    (memLoad mem (src + BitVec.ofNat 64 (16*j+8)) 64 ^^^ acc.2) y0 y1) initial

theorem rawUpdateBlocks_four (mem : Ram) (src y0 y1 : BitVec 64)
    (initial : BitVec 64 × BitVec 64) :
    rawUpdateBlocks mem src 4 y0 y1 initial =
      let a := polyvalMultiplyWords (memLoad mem src 64 ^^^ initial.1)
        (memLoad mem (src + 8) 64 ^^^ initial.2) y0 y1
      let b := polyvalMultiplyWords (memLoad mem (src + 16) 64 ^^^ a.1)
        (memLoad mem (src + 24) 64 ^^^ a.2) y0 y1
      let c := polyvalMultiplyWords (memLoad mem (src + 32) 64 ^^^ b.1)
        (memLoad mem (src + 40) 64 ^^^ b.2) y0 y1
      polyvalMultiplyWords (memLoad mem (src + 48) 64 ^^^ c.1)
        (memLoad mem (src + 56) 64 ^^^ c.2) y0 y1 := by
  unfold rawUpdateBlocks
  rw [show List.range 4 = [0,1,2,3] from by decide +kernel]
  simp only [List.foldl_cons, List.foldl_nil, Nat.reduceMul, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero]


theorem rawUpdateBlocks_eq_updateBlocks (raw mem : Ram) (srcRaw src y0 y1 : BitVec 64)
    (n : Nat) (initial : BitVec 64 × BitVec 64)
    (h0 : ∀ j < n, memLoad raw (srcRaw + BitVec.ofNat 64 (16*j)) 64 =
      bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j+8)) 64))
    (h1 : ∀ j < n, memLoad raw (srcRaw + BitVec.ofNat 64 (16*j+8)) 64 =
      bswapSpec (memLoad mem (src + BitVec.ofNat 64 (16*j)) 64)) :
    rawUpdateBlocks raw srcRaw n y0 y1 initial = updateBlocks mem src n y0 y1 initial := by
  unfold rawUpdateBlocks updateBlocks
  apply foldl_congr_on
  intro acc j hj
  rw [h0 j (List.mem_range.mp hj), h1 j (List.mem_range.mp hj)]
  rw [BitVec.xor_comm _ acc.1, BitVec.xor_comm _ acc.2]


end AesGcm.Proofs.Machine.GHASHUpdate
