import K256.Proofs.Verify.Hash.Blocks
import Standards.SECG.ECC.Encoding
import K256.Proofs.Verify.Hash.Padding.Encoding
import K256.Proofs.Verify.Hash.Padding.Standard.Parsing

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

theorem blockBits_eq_extract (input : ByteArray) (index : Nat) :
    blockBits input index =
      (Standards.NIST.SHA2.bytesToBits input).extract (512 * index) (512 * (index + 1)) := by
  rw [blockBits, bytesToBits_extract]
  congr 1 <;> omega

private theorem vector_ofFn_hashWords (hash : Vector (BitVec 32) 8) :
    (Vector.ofFn fun i : Fin 8 => (hash.toArray.map UInt32.ofBitVec)[i.val]!.toBitVec) =
      hash := by
  apply Vector.ext
  intro i hi
  simp

theorem compressBlocksFrom_eq_foldl (hash : Array UInt32) (input : ByteArray)
    (start count : Nat) :
    compressBlocksFrom hash input start count =
      (List.range' start count).foldl (fun hash i => Reference.compress hash (blockBits input i)) hash := by
  induction count generalizing hash start with
  | zero => rfl
  | succ count ih =>
      simp only [compressBlocksFrom, List.range'_succ, List.foldl_cons, ih]

private theorem parse_eq_map_range (bits : Array Bool) :
    Standards.NIST.SHA2.SHA256.parse bits =
      (Array.range (bits.size / 512)).map (fun i => (Standards.NIST.SHA2.SHA256.parse bits)[i]!) := by
  apply Array.ext
  · simp [Standards.NIST.SHA2.SHA256.parse]
  · intro i hi hi'
    simp only [Standards.NIST.SHA2.SHA256.parse, Array.size_ofFn] at hi
    simp [hi, Standards.NIST.SHA2.SHA256.parse]

private theorem fold_compress_eq_hashComputation
    (input : ByteArray) (bits : Array Bool) (H : Vector (BitVec 32) 8)
    (hsize : bits.size / 512 = input.size / 64)
    (hparse : ∀ i, i < bits.size / 512 →
      (Standards.NIST.SHA2.SHA256.parse bits)[i]! =
        Vector.ofFn (fun j : Fin 16 => BitVec.ofNat 32
          (Reference.bitsToNat ((blockBits input i).extract (32*j.val) (32*(j.val+1)))))) :
    compressBlocks (H.toArray.map UInt32.ofBitVec) input =
      (Standards.NIST.SHA2.SHA256.hashComputation
        (Standards.NIST.SHA2.SHA256.parse bits) H).toArray.map UInt32.ofBitVec := by
  rw [compressBlocks, compressBlocksFrom_eq_foldl]
  unfold Standards.NIST.SHA2.SHA256.hashComputation
  rw [parse_eq_map_range, Array.foldl_map, ← Array.foldl_toList, Array.toList_range,
    List.range_eq_range']
  rw [hsize]
  apply List.foldl_rel (r := fun (a : Array UInt32) (b : Vector (BitVec 32) 8) => a = b.toArray.map UInt32.ofBitVec) rfl
  intro i hi a b hab
  subst a
  have hi' : i < bits.size / 512 := by
    rw [List.mem_range'_1] at hi
    omega
  rw [hparse i hi']
  unfold Reference.compress
  rw [vector_ofFn_hashWords]

theorem compressBlocks_eq_hashComputation (input : ByteArray) (H : Vector (BitVec 32) 8) :
    compressBlocks (H.toArray.map UInt32.ofBitVec) input =
      (Standards.NIST.SHA2.SHA256.hashComputation
        (Standards.NIST.SHA2.SHA256.parse (Standards.NIST.SHA2.bytesToBits input)) H).toArray.map
          UInt32.ofBitVec := by
  apply fold_compress_eq_hashComputation
  · rw [bytesToBits_size]
    exact Nat.mul_div_mul_left input.size 64 (by decide : 0 < 8)
  · intro i hi
    rw [getElem!_pos _ i (by
      simpa only [Standards.NIST.SHA2.SHA256.parse, Array.size_ofFn] using hi)]
    rw [parse_getElem_eq_blockWords _ i hi, blockBits_eq_extract]

end K256.Proofs.Verify.Hash
