import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Bytes
import Sha2.Proofs.Common.SHA512.Interfaces

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

def serializeHash (hash : Array UInt64) : ByteArray :=
  hash.foldl (fun output word => output ++ Encoding.natToOctets 8 word.toNat) ByteArray.empty

theorem blockBits_eq_extract (input : ByteArray) (index : Nat) :
    blockBits input index =
      (Encoding.octetsToBits input).extract (1024 * index) (1024 * (index + 1)) := by
  rw [blockBits, octetsToBits_extract]
  congr 1 <;> omega

theorem compressBlocksFrom_eq_foldl (hash : Array UInt64) (input : ByteArray)
    (start count : Nat) :
    compressBlocksFrom hash input start count =
      (List.range' start count).foldl (fun hash i => SHA512.compress hash (blockBits input i)) hash := by
  induction count generalizing hash start with
  | zero => rfl
  | succ count ih =>
      simp only [compressBlocksFrom, List.range'_succ, List.foldl_cons, ih]

theorem serializeHash_compressBlocks_bytePadding (input : ByteArray) :
    serializeHash (compressBlocks SHA512.initialHash (bytePadding input)) = SHA512.sha512 input := by
  unfold SHA512.sha512 SHA512.sha512Bits
  change serializeHash (compressBlocks SHA512.initialHash (bytePadding input)) = Id.run (do
    let hash ← forIn [:(SHA512.pad (Encoding.octetsToBits input)).size / 1024]
      SHA512.initialHash (fun i hash => pure (ForInStep.yield
        (SHA512.compress hash ((SHA512.pad (Encoding.octetsToBits input)).extract
          (1024 * i) (1024 * (i + 1))))))
    pure (serializeHash hash))
  rw [← octetsToBits_bytePadding]
  simp only [octetsToBits_size, ← blockBits_eq_extract,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hsize : 8 * (bytePadding input).size / 1024 = (bytePadding input).size / 128 :=
    Nat.mul_div_mul_left (bytePadding input).size 128 (by decide : 0 < 8)
  simp only [hsize, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change serializeHash (compressBlocksFrom SHA512.initialHash (bytePadding input) 0
    ((bytePadding input).size / 128)) =
    serializeHash ((List.range' 0 ((bytePadding input).size / 128)).foldl
      (fun hash i => SHA512.compress hash (blockBits (bytePadding input) i)) SHA512.initialHash)
  rw [compressBlocksFrom_eq_foldl]

theorem serializeHash_compressBlocks_bytePadding384 (input : ByteArray) :
    serializeHash ((compressBlocks SHA512.initialHash384 (bytePadding input)).extract 0 6) = SHA512.sha384 input := by
  unfold SHA512.sha384 SHA512.sha384Bits
  change serializeHash ((compressBlocks SHA512.initialHash384 (bytePadding input)).extract 0 6) = Id.run (do
    let hash ← forIn [:(SHA512.pad (Encoding.octetsToBits input)).size / 1024]
      SHA512.initialHash384 (fun i hash => pure (ForInStep.yield
        (SHA512.compress hash ((SHA512.pad (Encoding.octetsToBits input)).extract
          (1024 * i) (1024 * (i + 1))))))
    pure (serializeHash (hash.extract 0 6)))
  rw [← octetsToBits_bytePadding]
  simp only [octetsToBits_size, ← blockBits_eq_extract,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hsize : 8 * (bytePadding input).size / 1024 = (bytePadding input).size / 128 :=
    Nat.mul_div_mul_left (bytePadding input).size 128 (by decide : 0 < 8)
  simp only [hsize, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change serializeHash ((compressBlocksFrom SHA512.initialHash384 (bytePadding input) 0
    ((bytePadding input).size / 128)).extract 0 6) =
    serializeHash (((List.range' 0 ((bytePadding input).size / 128)).foldl
      (fun hash i => SHA512.compress hash (blockBits (bytePadding input) i)) SHA512.initialHash384).extract 0 6)
  rw [compressBlocksFrom_eq_foldl]

end Sha2.Proofs.Common.SHA512
