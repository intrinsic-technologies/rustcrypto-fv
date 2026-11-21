import Sha3.Proofs.Incremental.State

namespace Sha3.Proofs.Incremental

open Keccak Absorption

theorem padded_block_eq (rate : Nat) (input : ByteArray) (hr : 0 < rate) (suffix : UInt8 := 0x06) :
    blockLanes (paddedBytes rate input suffix) (input.size / rate * rate) rate =
      fun lane ↦ (blockLanes input (input.size / rate * rate) rate lane ^^^
        byteLanes (input.size % rate) suffix lane) ^^^ byteLanes (rate - 1) 0x80 lane := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_blockLanes_final rate input hr lane ⟨z, hz⟩ suffix]
  simp only [BitVec.getLsbD_xor, blockLanes, byteLanes, getLsbD_packLane _ ⟨z, hz⟩]
  have hmod := Nat.mod_lt input.size hr
  have hdiv := Nat.div_add_mod input.size rate
  rw [Nat.mul_comm rate] at hdiv
  have hread : input.size / rate * rate + (8 * lane.val + z / 8) < input.size ↔
      8 * lane.val + z / 8 < input.size % rate := by omega
  have hlast : 8 * lane.val + z / 8 + 1 = rate ↔
      8 * lane.val + z / 8 = rate - 1 := by omega
  simp only [hread, hlast]
  by_cases hj : 8 * lane.val + z / 8 < rate
  · simp only [hj, true_and, ↓reduceDIte]
    simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    congr 2 <;> split <;> simp
  · have hrem : ¬ 8 * lane.val + z / 8 < input.size % rate := by omega
    have hfirst : ¬ 8 * lane.val + z / 8 = input.size % rate := by omega
    have hfinal : ¬ 8 * lane.val + z / 8 = rate - 1 := by omega
    simp [hj, hrem, hfirst, hfinal]

theorem finalize_canonicalState (permute : Lanes → Lanes) (rate : Nat)
    (hr : 0 < rate) (input : ByteArray) (suffix : UInt8 := 0x06) :
    finalize permute rate (canonicalState permute rate input) suffix =
      absorbSha3 permute rate input suffix := by
  rw [absorbSha3_eq_completeBlocks permute rate input hr suffix, padded_block_eq rate input hr suffix]
  unfold finalize canonicalState
  congr 1
  funext lane
  simp only [BitVec.xor_assoc]

theorem digest_finalize_sha3_224 (input : ByteArray) :
    digestLanes (finalize keccakLanes 144 (canonicalState keccakLanes 144 input))
      28 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Standards.NIST.SHA3.SHA3_224 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 144 (by decide) input]
  exact digestLanes_sha3_224 input

theorem digest_finalize_sha3_256 (input : ByteArray) :
    digestLanes (finalize keccakLanes 136 (canonicalState keccakLanes 136 input))
      32 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Standards.NIST.SHA3.SHA3_256 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 136 (by decide) input]
  exact digestLanes_sha3_256 input

theorem digest_finalize_sha3_384 (input : ByteArray) :
    digestLanes (finalize keccakLanes 104 (canonicalState keccakLanes 104 input))
      48 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Standards.NIST.SHA3.SHA3_384 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 104 (by decide) input]
  exact digestLanes_sha3_384 input

theorem digest_finalize_sha3_512 (input : ByteArray) :
    digestLanes (finalize keccakLanes 72 (canonicalState keccakLanes 72 input))
      64 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Standards.NIST.SHA3.SHA3_512 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 72 (by decide) input]
  exact digestLanes_sha3_512 input


theorem digest_finalize_keccak224 (input : ByteArray) :
    digestLanes (finalize keccakLanes 144 (canonicalState keccakLanes 144 input) 0x01)
      28 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Sha3.Spec.Keccak.keccak224 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 144 (by decide) input 0x01]
  exact digestLanes_keccak224 input

theorem digest_finalize_keccak256 (input : ByteArray) :
    digestLanes (finalize keccakLanes 136 (canonicalState keccakLanes 136 input) 0x01)
      32 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Sha3.Spec.Keccak.keccak256 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 136 (by decide) input 0x01]
  exact digestLanes_keccak256 input

theorem digest_finalize_keccak384 (input : ByteArray) :
    digestLanes (finalize keccakLanes 104 (canonicalState keccakLanes 104 input) 0x01)
      48 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Sha3.Spec.Keccak.keccak384 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 104 (by decide) input 0x01]
  exact digestLanes_keccak384 input

theorem digest_finalize_keccak512 (input : ByteArray) :
    digestLanes (finalize keccakLanes 72 (canonicalState keccakLanes 72 input) 0x01)
      64 (by decide) = Standards.NIST.SHA3.Digest.ofBits
        (Sha3.Spec.Keccak.keccak512 (Standards.NIST.SHA3.bytesToBits input)) := by
  rw [finalize_canonicalState keccakLanes 72 (by decide) input 0x01]
  exact digestLanes_keccak512 input

end Sha3.Proofs.Incremental
