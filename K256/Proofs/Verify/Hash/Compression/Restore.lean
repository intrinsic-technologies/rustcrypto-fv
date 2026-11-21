import K256.Proofs.Verify.Hash.Compression.Return
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private def storeHashTail (m : Ram) (dst : BitVec 64) (hash : Array UInt32) : Nat → Ram
  | 0 => m
  | n + 1 => memStore (storeHashTail m dst hash n) (wordAddr dst 32 (n + 1))
      hash[n + 1]!.toBitVec

private def storeHashWords (m : Ram) (dst : BitVec 64) (hash : Array UInt32) : Ram :=
  memStore (storeHashTail m dst hash 7) dst hash[0]!.toBitVec

private theorem wordAddr_toNat {dst : BitVec 64} (low : dst.toNat + 32 ≤ 2^32)
    {i : Nat} (hi : i < 8) : (wordAddr dst 32 i).toNat = dst.toNat + 4 * i := by
  simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := 4 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem wordApart {dst : BitVec 64} (low : dst.toNat + 32 ≤ 2^32)
    {i j : Nat} (hi : i < 8) (hj : j < 8) (hne : i ≠ j) :
    RangeApart (wordAddr dst 32 i) 4 (wordAddr dst 32 j) 4 := by
  apply RangeApart.of_toNat <;> simp only [wordAddr_toNat low hi, wordAddr_toNat low hj] <;> omega

private theorem storeHashTail_load (m : Ram) (dst : BitVec 64) (hash : Array UInt32)
    (low : dst.toNat + 32 ≤ 2^32) {i n : Nat} (pos : 0 < i) (hi : i ≤ n) (hn : n < 8) :
    memLoad (storeHashTail m dst hash n) (wordAddr dst 32 i) 32 = hash[i]!.toBitVec := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [storeHashTail]
    by_cases h : i = n + 1
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (wordApart low hn (by omega) (Ne.symm h))]
      exact ih (by omega) (by omega)

private theorem storeHashWords_words (m : Ram) (dst : BitVec 64) (hash : Array UInt32)
    (low : dst.toNat + 32 ≤ 2^32) (size : hash.size = 8) : StateAt (storeHashWords m dst hash) dst hash := by
  refine ⟨size, fun i hi => ?_⟩
  rw [Vector.getElem_ofFn, storeHashWords]
  have h₀ : wordAddr dst 32 0 = dst := BitVec.add_zero dst
  by_cases h : i = 0
  · subst i
    rw [h₀]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _]
    · exact storeHashTail_load m dst hash low (by omega) (by omega) (by decide)
    · simpa only [h₀] using wordApart low (i := 0) (by decide) hi (Ne.symm h)

private theorem storeHashWords_frame (m : Ram) (dst : BitVec 64) (hash : Array UInt32)
    (low : dst.toNat + 32 ≤ 2^32) :
    RamWriteFrame m (storeHashWords m dst hash) [⟨dst.toNat, 32⟩] := by
  have inside (i : Nat) (hi : i < 8) : InRegions [⟨dst.toNat, 32⟩] (wordAddr dst 32 i) 4 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change dst.toNat ≤ (wordAddr dst 32 i).toNat ∧
      (wordAddr dst 32 i).toNat + 4 ≤ dst.toNat + 32 ∧ (wordAddr dst 32 i).toNat + 4 ≤ 2^64
    rw [wordAddr_toNat low hi]
    exact ⟨by omega, by omega, by omega⟩
  have tail {n : Nat} (hn : n < 8) : RamWriteFrame m (storeHashTail m dst hash n) [⟨dst.toNat, 32⟩] := by
    induction n with
    | zero => exact .refl _ _
    | succ n ih => exact (ih (by omega)).memStore _ (inside _ hn)
  exact (tail (by decide : 7 < 8)).memStore _ (by simpa only [wordAddr, Nat.mul_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] using inside 0 (by decide))

private theorem get64_setWidth32 (v : Value) : (v.get 64).setWidth 32 = v.get 32 :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

private theorem value_get64 (v : Value) (h : v.width = 64) : (⟨64, v.get 64⟩ : Value) = v := by
  cases v with
  | mk width bits =>
    change width = 64 at h
    subst width
    rw [Value.get, BitVec.setWidth_eq]

private theorem savedSlot_bounds : ∀ i : Fin 6,
    ((#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i]).toNat ≤ 336 ∧
    ((#v[3, 5, 12, 13, 14, 15] : Vector (Fin Reg.count) 6)[i]).val ∈ [3, 5, 12, 13, 14, 15] := by
  decide

variable {entry : CFG.Values Value Reg.count} {original : Ram} {sp dst src : BitVec 64}
    {initial : Array UInt32} {input : ByteArray}

theorem restore (call : Call entry original sp dst src initial input)
    {hash : Array UInt32} {args : CFG.Values Value Reg.count} {mem : Ram}
    (ready : LoopState entry original sp dst src (input.size / 64) (input.size / 64)
      hash args mem) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1240c4, args, mem⟩, []⟩ out ∧
      Returned entry original sp dst hash out := by
  have stack := (call.stackWritable.of_frame ready.writes).readable
  have area := call.hashWritable.of_frame ready.writes
  have rsp := ready.rsp
  have destination : memLoad mem (sp - 144) 64 = dst := by
    rw [show sp - 144 = sp - 336 + 192 by bv_omega]
    exact ready.destination
  have word (i : Fin 8) := ready.words i
  have word0 : args[3].get 32 = hash[0]!.toBitVec := word 0
  have word1 : args[14].get 32 = hash[1]!.toBitVec := word 1
  have word2 : args[0].get 32 = hash[2]!.toBitVec := word 2
  have word3 : args[9].get 32 = hash[3]!.toBitVec := word 3
  have word4 : args[8].get 32 = hash[4]!.toBitVec := word 4
  have word5 : args[10].get 32 = hash[5]!.toBitVec := word 5
  have word6 : args[2].get 32 = hash[6]!.toBitVec := word 6
  have word7 : args[1].get 32 = hash[7]!.toBitVec := word 7
  have hashLow := area.readable.low
  have stackLow := call.returnReadable.low
  have depth := call.depth
  have hashStack := call.hashStack
  have writes := storeHashWords_frame mem dst hash hashLow
  have stackOutside {a : BitVec 64} (lo : sp.toNat - 336 ≤ a.toNat)
      (hi : a.toNat + 8 ≤ sp.toNat + 8) : Outside [⟨dst.toNat, 32⟩] a 8 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change a.toNat + 8 ≤ dst.toNat ∨ dst.toNat + 32 ≤ a.toNat
    rcases hashStack with h | h <;> omega
  have savedSlot (i : Fin 6) :
      (⟨64, memLoad (storeHashWords mem dst hash)
        (sp - (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i]) 64⟩ : Value) =
        entry[(#v[3, 5, 12, 13, 14, 15] : Vector (Fin Reg.count) 6)[i]] := by
    let off := (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i]
    have bound : off.toNat ≤ 336 := (savedSlot_bounds i).1
    have addr : (sp - off).toNat = sp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    have slot : Outside [⟨dst.toNat, 32⟩] (sp - off) 8 := by
      apply stackOutside <;> rw [addr] <;> omega
    change (⟨64, memLoad (storeHashWords mem dst hash) (sp - off) 64⟩ : Value) = _
    rw [writes.memLoad_eq slot, ready.slots i]
    exact value_get64 _ (call.savedWidths _ (savedSlot_bounds i).2)
  have branch : ∃ next : CFG.Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1240c4, args, mem⟩ =
        .jump ⟨.l1240f8, next, storeHashWords mem dst hash⟩ ∧
      next[4].get 64 = sp ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] → next[i] = entry[i] := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval
      simp only [rsp, Lift.reduceAddOffset, BitVec.sub_add_cancel, destination, get64_setWidth32,
        word0, word1, word2, word3, word4, word5, word6, word7]
      have included : ∀ x ∈ codeRange 0x1240c4 bytes_l1240c4, x ∈ Extracted.programImage :=
        fun x hx => Common.fnCode_subset_programImage x (code_l1240c4 x hx)
      simp (disch := slot_guard using included) only [ite_eq_left]
      rfl
    case post =>
      refine ⟨rfl, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h <;> subst i
      · exact savedSlot 0
      · exact savedSlot 1
      · exact savedSlot 2
      · exact savedSlot 3
      · exact savedSlot 4
      · exact savedSlot 5
      · exact ready.preserved 22 (by decide)
      · exact ready.preserved 39 (by decide)
      · exact ready.preserved 50 (by decide)
      · exact ready.preserved 51 (by decide)
  have returnWord : memLoad (storeHashWords mem dst hash) sp 64 = memLoad original sp 64 := by
    rw [writes.memLoad_eq (stackOutside (by omega) (by omega))]
    apply ready.writes.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change sp.toNat - 336 + 336 ≤ sp.toNat
    omega
  have fullFrame : RamWriteFrame original (storeHashWords mem dst hash) (footprint sp dst) := by
    refine ((RamWriteFrame.refl original (footprint sp dst)).trans ready.writes ?_).trans writes ?_
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨next, jump, rspNext, restored⟩ := branch
  obtain ⟨out, run, store, tag, rspOut, kept⟩ :=
    ret rspNext (call.returnReadable.of_frame fullFrame) (by rw [returnWord]; exact call.returnLow)
  refine ⟨out, .next (congrArg (Transfer.next _ []) jump) (.done (congrArg (Transfer.next _ []) run)),
    ⟨store ▸ storeHashWords_words mem dst hash hashLow ready.size, store ▸ fullFrame, ?_, rspOut,
      fun i hi => (kept i hi).trans (restored i hi)⟩⟩
  rw [tag, returnWord]

end K256.Proofs.Verify.Hash.Compression
