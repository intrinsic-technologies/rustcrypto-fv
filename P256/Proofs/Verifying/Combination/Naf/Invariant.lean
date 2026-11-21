import P256.Proofs.Verifying.Combination.Naf.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf

open Prelude X86 X86.Machine X86Proofs

theorem quotient_shift (n i k : Nat) : n / 2^i / 2^k = n / 2^(i+k) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem specification_even {n i c : Nat} {ds : List Int}
    (hi : i < 256) (length : ds.length = i)
    (specification : digits n = ds ++ recode (257-i) (256-i) (n/2^i) c)
    (even : (n/2^i % 32+c) % 2 = 0) :
    (ds ++ [0]).length = i+1 ∧
      digits n = (ds ++ [0]) ++ recode (257-(i+1)) (256-(i+1)) (n/2^(i+1)) c := by
  constructor
  · simp only [List.length_append, List.length_cons, List.length_nil, length]
  · have fuel : 257-i = (256-i)+1 := by omega
    rw [fuel, recode_even (by omega) even] at specification
    have fuel' : 256-i = 257-(i+1) := by omega
    have bits' : 256-i-1 = 256-(i+1) := by omega
    have quotient : n/2^i/2 = n/2^(i+1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    rw [bits', fuel', quotient] at specification
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using specification

theorem specification_odd {n i c : Nat} {ds : List Int}
    (hi : i < 256) (hn : n < 2^256) (hc : c ≤ 1) (length : ds.length = i)
    (specification : digits n = ds ++ recode (257-i) (256-i) (n/2^i) c)
    (odd : (n/2^i % 32+c) % 2 = 1) :
    let window := n/2^i % 32+c
    let count := skip (256-i) window
    (ds ++ [digit window] ++ List.replicate (count-1) 0).length = i+count ∧
      digits n = (ds ++ [digit window] ++ List.replicate (count-1) 0) ++
        recode (257-(i+count)) (256-(i+count)) (n/2^(i+count)) (carry window) := by
  let window := n/2^i % 32+c
  let count := skip (256-i) window
  have bound : n/2^i < 2^(256-i) := shifted_bound hn (by omega)
  have countBounds : 1 ≤ count ∧ count ≤ 256-i ∧ count ≤ 5 :=
    odd_skip_bounds (by omega) bound hc odd
  change (ds ++ [digit window] ++ List.replicate (count-1) 0).length = i+count ∧ _
  constructor
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, length]
    omega
  · have fuel : 257-i = (256-i)+1 := by omega
    rw [fuel, recode_odd (by omega) bound hc odd] at specification
    change digits n = ds ++ digit window :: (List.replicate (count-1) 0 ++
      recode (256-i-count+1) (256-i-count) (n/2^i/2^count) (carry window)) at specification
    have fuel' : 256-i-count+1 = 257-(i+count) := by omega
    have bits' : 256-i-count = 256-(i+count) := by omega
    rw [fuel', bits', quotient_shift] at specification
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using specification

theorem output_append_segment {s t : RamState} {address : BitVec 64} {ds added : List Int}
    (output : DigitsAt s address ds) (bound : address.toNat+257 ≤ 2^32)
    (room : ds.length+added.length ≤ 257)
    (written : Bytes t.external (address+BitVec.ofNat 64 ds.length) added.length
      (fun i => UInt8.ofBitVec (BitVec.ofInt 8 ((added[i]?).getD 0))))
    (frame : MemoryWriteFrame s t
      #v[⟨(address+BitVec.ofNat 64 ds.length).toNat, added.length⟩]) :
    DigitsAt t address (ds++added) := by
  have kept (i : Nat) (hi : i<257) (outside : i<ds.length ∨ ds.length+added.length ≤ i) :
      memLoad t.external (address+BitVec.ofNat 64 i) 8 =
        memLoad s.external (address+BitVec.ofNat 64 i) 8 := by
    have bytes := frame (address+BitVec.ofNat 64 i) (by
      intro region hr hin
      have hr' : region = ⟨(address+BitVec.ofNat 64 ds.length).toNat, added.length⟩ := by simpa using hr
      subst region
      change (address+BitVec.ofNat 64 ds.length).toNat ≤ (address+BitVec.ofNat 64 i).toNat ∧
        (address+BitVec.ofNat 64 i).toNat < (address+BitVec.ofNat 64 ds.length).toNat+added.length at hin
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hin
      omega)
    rw [memLoad_8, memLoad_8]
    exact congrArg (fun byte : Option UInt8 => (byte.getD 0).toBitVec) bytes
  intro i hi
  by_cases before : i<ds.length
  · rw [List.getElem?_append_left before, kept i hi (.inl before)]
    exact output i hi
  · rw [List.getElem?_append_right (by omega)]
    by_cases inside : i-ds.length < added.length
    · have value := written.loadByte (i-ds.length) inside
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega : ds.length ≤ i),
        UInt8.toBitVec_ofBitVec] using value
    · rw [kept i hi (.inr (by omega)), output i hi,
        List.getElem?_eq_none (by omega : ds.length ≤ i),
        List.getElem?_eq_none (by omega : added.length ≤ i-ds.length)]

end P256.Proofs.Verifying.Combination.Naf
