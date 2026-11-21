import K256.Proofs.Signing.UpdateV.Finalize.State
import K256.Proofs.Verify.Hash.Output
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR K256.Proofs.Verify.Hash

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem returnBlock {a : Registers} {m : Ram} {base dst : BitVec 64} {hash : Array UInt32}
    (rsp : a[4] = ⟨64,base⟩) (rbx : a[3] = ⟨64,dst⟩)
    (read : Readable m base 368) (write : Writable Extracted.programImage m dst 32)
    (above : base.toNat + 368 ≤ dst.toNat)
    (retLow : (memLoad m (base + 360) 64).toNat < 2^32)
    (h : Compression.StateAt m (base + 72) hash) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l107f2b,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,memLoad m (base + 360) 64⟩ ∧
      out.values[4] = ⟨64,base + 368⟩ ∧
      (∀ i : Fin 6, out.values[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[i]] =
        ⟨64,memLoad m (base + (#v[312,352,320,328,336,344] : Vector (BitVec 64) 6)[i]) 64⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨dst.toNat,32⟩] ∧
      (⟨dst.toNat,32⟩ : MemoryRegion).HasBytes out.store (serializeHash hash) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,6,7,8,9] → out.values[i].width = 64) := by
  have rspBits : a[4].get 64 = base := congrArg (Value.get 64) rsp
  have dstBits : a[3].get 64 = dst := congrArg (Value.get 64) rbx
  have word (i : Nat) (hi : i < 8) :
      memLoad m (wordAddr (base + 72) 32 i) 32 = hash[i]!.toBitVec := by
    have eq := h.2 i hi
    rw [Vector.getElem_ofFn] at eq
    exact eq
  have word0 := word 0 (by decide)
  have word1 := word 1 (by decide)
  have word2 := word 2 (by decide)
  have word3 := word 3 (by decide)
  have word4 := word 4 (by decide)
  have word5 := word 5 (by decide)
  have word6 := word 6 (by decide)
  have word7 := word 7 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at word0 word1 word2 word3 word4 word5 word6 word7
  have inside (i : Nat) (hi : i < 8) : InRegions [⟨dst.toNat,32⟩] (wordAddr dst 32 i) 4 := by
    have low := write.readable.low
    have addr : (wordAddr dst 32 i).toNat = dst.toNat + 4 * i := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (a := 4 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨_, List.mem_cons_self, ?_⟩
    change dst.toNat ≤ (wordAddr dst 32 i).toNat ∧
      (wordAddr dst 32 i).toNat + 4 ≤ dst.toNat + 32 ∧ (wordAddr dst 32 i).toNat + 4 ≤ 2^64
    rw [addr]
    exact ⟨by omega, by omega, by omega⟩
  have frame (n : Nat) (hn : n ≤ 8) :
      RamWriteFrame m (storeDigestWords m dst hash n) [⟨dst.toNat,32⟩] :=
    storeDigestWords_frame fun i hi => inside i (by omega)
  have savedFrame := frame 8 (by decide)
  have stackLow := read.low
  have stackAddr (off : BitVec 64) (bound : off.toNat ≤ 368) :
      (base + off).toNat = base.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have keep (off : BitVec 64) (bound : off.toNat + 8 ≤ 368) :
      memLoad (storeDigestWords m dst hash 8) (base + off) 64 = memLoad m (base + off) 64 := by
    apply savedFrame.memLoad_eq
    have addr := stackAddr off (by omega)
    refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    left
    change (base + off).toNat + 8 ≤ dst.toNat
    rw [addr]
    omega
  have keep312 := keep 312 (by decide)
  have keep320 := keep 320 (by decide)
  have keep328 := keep 328 (by decide)
  have keep336 := keep 336 (by decide)
  have keep344 := keep 344 (by decide)
  have keep352 := keep 352 (by decide)
  have keep360 := keep 360 (by decide)
  simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero] at keep312 keep320 keep328 keep336 keep344 keep352 keep360
  have inputLoad (off : BitVec 64) (bound : off.toNat + 4 ≤ 368) :
      LoadOk m (base + off) 4 := by
    apply LoadOk.of_region read <;> rw [stackAddr off (by omega)] <;> omega
  have savedLoad (off : BitVec 64) (bound : off.toNat + 8 ≤ 368) :
      LoadOk (storeDigestWords m dst hash 8) (base + off) 8 := by
    apply LoadOk.of_region (read.of_frame savedFrame) <;> rw [stackAddr off (by omega)] <;> omega
  have outputStore (i off len : Nat) (hi : i < 8) (hc : off + len ≤ bytes_l107f2b.length) :
      StoreOk Extracted.programImage (storeDigestWords m dst hash i) (wordAddr dst 32 i) 4
        (0x107f2b + BitVec.ofNat 64 off) len := by
    obtain ⟨r, hr, lo, high, _⟩ := inside i hi
    obtain rfl := List.mem_singleton.mp hr
    exact ParseSignature.storeOk_of_codeRange ((write.sub lo high).of_frame (frame i (by omega)))
      (fun x hx => Common.fnCode_subset_programImage x (code_l107f2b x hx)) hc
  have input72 := inputLoad 72 (by decide)
  have input76 := inputLoad 76 (by decide)
  have input80 := inputLoad 80 (by decide)
  have input84 := inputLoad 84 (by decide)
  have input88 := inputLoad 88 (by decide)
  have input92 := inputLoad 92 (by decide)
  have input96 := inputLoad 96 (by decide)
  have input100 := inputLoad 100 (by decide)
  have store0 := outputStore 0 54 2 (by decide) (by decide +kernel)
  have store1 := outputStore 1 56 3 (by decide) (by decide +kernel)
  have store2 := outputStore 2 59 3 (by decide) (by decide +kernel)
  have store3 := outputStore 3 62 3 (by decide) (by decide +kernel)
  have store4 := outputStore 4 65 3 (by decide) (by decide +kernel)
  have store5 := outputStore 5 68 4 (by decide) (by decide +kernel)
  have store6 := outputStore 6 72 4 (by decide) (by decide +kernel)
  have store7 := outputStore 7 76 4 (by decide) (by decide +kernel)
  have saved312 := savedLoad 312 (by decide)
  have saved320 := savedLoad 320 (by decide)
  have saved328 := savedLoad 328 (by decide)
  have saved336 := savedLoad 336 (by decide)
  have saved344 := savedLoad 344 (by decide)
  have saved352 := savedLoad 352 (by decide)
  have saved360 := savedLoad 360 (by decide)
  simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.reduceAdd] at store0 store1 store2 store3 store4 store5 store6 store7
  simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero] at saved312 saved320 saved328 saved336 saved344 saved352 saved360
  have retLow' : (memLoad m (base + 360#64) 64).toNat < 2^32 := retLow
  simp only [BitVec.ofNat_eq_ofNat] at input72 input76 input80 input84 input88 input92 input96 input100
  have bytes := storeDigestWords_hasBytes m dst h.1
  simp only [storeDigestWords, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.add_zero] at savedFrame bytes
  refine ⟨?_, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval [rspBits, dstBits]
    simp only [BitVec.ofNat_eq_ofNat, word0, word1, word2, word3, word4, word5, word6, word7,
      input72, input76, input80, input84, input88, input92, input96, input100,
      store0, store1, store2, store3, store4, store5, store6, store7,
      saved312, saved320, saved328, saved336, saved344, saved352, saved360,
      keep312, keep320, keep328, keep336, keep344, keep352, keep360, retLow', and_self, ↓reduceIte]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, ?_, savedFrame, bytes, ?_⟩
    · have cases : ∀ i : Fin 6, i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
          i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by decide
      rintro ⟨i, hi⟩
      rcases cases ⟨i, hi⟩ with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨i, hi⟩ member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.UpdateV.Finalize
