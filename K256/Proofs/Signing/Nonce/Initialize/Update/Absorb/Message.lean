import K256.Proofs.Signing.UpdateV.State

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb

open K256.Proofs.Verify.Hash Standards.NIST.SHA2

theorem compressBlocks_append_short (hash : Array UInt32) (full tail : ByteArray)
    (aligned : full.size % 64 = 0) (short : tail.size < 64) :
    compressBlocks hash (full ++ tail) = compressBlocks hash full := by
  rw [compressBlocks_append _ _ _ aligned]
  simp only [compressBlocks, Nat.div_eq_of_lt short, compressBlocksFrom]

theorem remainderBytes_append_short (full tail : ByteArray)
    (aligned : full.size % 64 = 0) (short : tail.size < 64) :
    remainderBytes (full ++ tail) = tail := by
  have cut : 64 * ((full ++ tail).size / 64) = full.size := by
    rw [ByteArray.size_append]
    omega
  rw [remainderBytes, cut, ByteArray.size_append]
  exact ByteArray.extract_append_eq_right rfl rfl

theorem remainderBytes_append_within (input extra : ByteArray)
    (fits : input.size % 64 + extra.size < 64) :
    remainderBytes (input ++ extra) = remainderBytes input ++ extra := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes input, ByteArray.append_assoc]
  apply remainderBytes_append_short
  · rw [fullBlocks_size]
    omega
  · rwa [ByteArray.size_append, remainderBytes_size]

theorem compressBlocks_append_within (hash : Array UInt32) (input extra : ByteArray)
    (fits : input.size % 64 + extra.size < 64) :
    compressBlocks hash (input ++ extra) = compressBlocks hash input := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes input, ByteArray.append_assoc]
  rw [compressBlocks_append_short, compressBlocks_fullBlocks]
  · rw [fullBlocks_size]
    omega
  · rwa [ByteArray.size_append, remainderBytes_size]

theorem append_crossing (hash : Array UInt32) (input extra : ByteArray) (cut : Nat)
    (fill : input.size % 64 + cut = 64) (inside : cut ≤ extra.size)
    (short : extra.size - cut < 64) :
    compressBlocks hash (input ++ extra) =
      Reference.compress (compressBlocks hash input)
        (bytesToBits (remainderBytes input ++ extra.extract 0 cut)) ∧
    remainderBytes (input ++ extra) = extra.extract cut extra.size := by
  let block := remainderBytes input ++ extra.extract 0 cut
  let tail := extra.extract cut extra.size
  have bs : block.size = 64 := by
    simpa only [block, ByteArray.size_append, remainderBytes_size, ByteArray.size_extract,
      Nat.min_eq_left inside, Nat.sub_zero] using fill
  have ts : tail.size < 64 := by
    simpa only [tail, ByteArray.size_extract, Nat.min_self] using short
  have split : (fullBlocks input ++ block) ++ tail = input ++ extra := by
    simp only [block, tail, ByteArray.append_assoc]
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right inside, ByteArray.extract_zero_size, ← ByteArray.append_assoc,
      fullBlocks_append_remainderBytes]
  have fa : (fullBlocks input).size % 64 = 0 := by rw [fullBlocks_size]; omega
  have ba : (fullBlocks input ++ block).size % 64 = 0 := by rw [ByteArray.size_append,bs]; omega
  rw [← split, compressBlocks_append_short _ _ _ ba ts, remainderBytes_append_short _ _ ba ts,
    compressBlocks_append _ _ _ fa, compressBlocks_fullBlocks, compressBlocks_single _ _ bs]
  exact ⟨rfl,rfl⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb
