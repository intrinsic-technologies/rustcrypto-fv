import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Bytes
import Hkdf.Proofs.Common.SHA256.Interfaces

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.NIST

def serializeHash (hash : Array UInt32) : ByteArray :=
  hash.foldl (fun output word => output ++ Encoding.natToOctets 4 word.toNat) ByteArray.empty

theorem blockBits_eq_extract (input : ByteArray) (index : Nat) :
    blockBits input index =
      (Encoding.octetsToBits input).extract (512 * index) (512 * (index + 1)) := by
  rw [blockBits, octetsToBits_extract]
  congr 1 <;> omega

theorem compressBlocksFrom_eq_foldl (hash : Array UInt32) (input : ByteArray)
    (start count : Nat) :
    compressBlocksFrom hash input start count =
      (List.range' start count).foldl (fun hash i => SHA256.compress hash (blockBits input i)) hash := by
  induction count generalizing hash start with
  | zero => rfl
  | succ count ih =>
      simp only [compressBlocksFrom, List.range'_succ, List.foldl_cons, ih]

theorem serializeHash_compressBlocks_bytePadding (input : ByteArray) :
    serializeHash (compressBlocks SHA256.initialHash (bytePadding input)) = SHA256.sha256 input := by
  unfold SHA256.sha256 SHA256.sha256Bits
  change serializeHash (compressBlocks SHA256.initialHash (bytePadding input)) = Id.run (do
    let hash ← forIn [:(SHA256.pad (Encoding.octetsToBits input)).size / 512]
      SHA256.initialHash (fun i hash => pure (ForInStep.yield
        (SHA256.compress hash ((SHA256.pad (Encoding.octetsToBits input)).extract
          (512 * i) (512 * (i + 1))))))
    pure (serializeHash hash))
  rw [← octetsToBits_bytePadding]
  simp only [octetsToBits_size, ← blockBits_eq_extract,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hsize : 8 * (bytePadding input).size / 512 = (bytePadding input).size / 64 :=
    Nat.mul_div_mul_left (bytePadding input).size 64 (by decide : 0 < 8)
  simp only [hsize, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change serializeHash (compressBlocksFrom SHA256.initialHash (bytePadding input) 0
    ((bytePadding input).size / 64)) =
    serializeHash ((List.range' 0 ((bytePadding input).size / 64)).foldl
      (fun hash i => SHA256.compress hash (blockBits (bytePadding input) i)) SHA256.initialHash)
  rw [compressBlocksFrom_eq_foldl]

end Hkdf.Proofs.Common.SHA256
