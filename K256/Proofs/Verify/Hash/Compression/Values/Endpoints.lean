import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants
import K256.Proofs.Verify.Hash.Compression.Mathematics.CompressionState

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

theorem invariant00_of_hashState {values : Values} {h : BitVecState} (block : Array Bool)
    (initial : hashState values = h) : invariant00 h block values :=
  ⟨congrArg BitVecState.c initial, congrArg BitVecState.h initial,
    congrArg BitVecState.g initial, congrArg BitVecState.a initial,
    congrArg BitVecState.e initial, congrArg BitVecState.d initial,
    congrArg BitVecState.f initial, congrArg BitVecState.b initial⟩

theorem compress_of_invariant53 {hash : Array UInt32} {block : Array Bool} {values : Values}
    (final : invariant53 (BitVecState.ofState (K256.Proofs.Verify.Hash.Compression.State.ofArray hash)) block values) :
    hashState values = BitVecState.ofState (K256.Proofs.Verify.Hash.Compression.State.ofArray (Reference.compress hash block)) := by
  let h := BitVecState.ofState (K256.Proofs.Verify.Hash.Compression.State.ofArray hash)
  change invariant53 h block values at final
  rw [compress_bitVecState, rounds_words]
  change hashState values =
    ⟨h.a + a h block 64, h.b + a h block 63, h.c + a h block 62, h.d + a h block 61,
      h.e + e h block 64, h.f + e h block 63, h.g + e h block 62, h.h + e h block 61⟩
  rcases final with ⟨h0, h1, h2, h3, h8, h9, h10, h14⟩
  rw [← a64] at h3
  rw [← e64] at h8
  simp only [hashState, h0, h1, h2, h3, h8, h9, h10, h14, BitVec.add_comm]

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
