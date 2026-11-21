import K256.Proofs.Verify.Hash.Compression.Reference
import K256.Proofs.Verify.Hash.Compression.Mathematics.BitVecModel
import K256.Proofs.Verify.Hash.Compression.Mathematics.Equivalence

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression

theorem compress_bitVecState (hash : Array UInt32) (block : Array Bool) :
    BitVecState.ofState (State.ofArray (Reference.compress hash block)) =
      let final := bitVecRounds (BitVecState.ofState (State.ofArray hash))
        ((schedule block).map UInt32.toBitVec) 64
      ⟨hash[0]!.toBitVec + final.a, hash[1]!.toBitVec + final.b,
        hash[2]!.toBitVec + final.c, hash[3]!.toBitVec + final.d,
        hash[4]!.toBitVec + final.e, hash[5]!.toBitVec + final.f,
        hash[6]!.toBitVec + final.g, hash[7]!.toBitVec + final.h⟩ := by
  rw [← compressModel_eq_compress, bitVecRounds_ofState]
  rfl

end K256.Proofs.Verify.Hash.Compression
