import Sha3.Proofs.LaneMemory
import Sha3.Proofs.Incremental.Basic

namespace Sha3.Proofs.Finalize.Padding

open X86 X86.Machine X86Proofs

theorem padded_state_eq {s : RamState} {pointer : BitVec 64}
    (a : Keccak.Lanes) (cursor rate : Nat) (hr : 0 < rate)
    (initial : Nat → UInt8)
    (hvalues : ∀ lane : Fin 25, ∀ j : Fin 8,
      initial (8 * lane.val + j.val) = storedByte (a lane) j.val)
    {suffix : UInt8}
    (hbytes : Bytes s.external pointer 200 (fun i ↦
      (initial i ^^^ (if i = cursor then suffix else 0)) ^^^
        (if i + 1 = rate then 0x80 else 0))) :
    Permutation.memoryLanes pointer s = fun lane ↦
      (a lane ^^^ Incremental.byteLanes cursor suffix lane) ^^^
        Incremental.byteLanes (rate - 1) 0x80 lane := by
  apply LaneMemory.memoryLanes_eq_of_byteFunction pointer s _ _ hbytes
  intro lane j
  rw [storedByte_xor, storedByte_xor, hvalues,
    storedByte_eq_extract (Incremental.byteLanes cursor suffix lane),
    Incremental.byteLanes_extract_byte,
    storedByte_eq_extract (Incremental.byteLanes (rate - 1) 0x80 lane),
    Incremental.byteLanes_extract_byte]
  have hlast : 8 * lane.val + j.val + 1 = rate ↔
      8 * lane.val + j.val = rate - 1 := by omega
  simp only [hlast]

theorem padded_memoryLanes_eq {s t : RamState} {pointer : BitVec 64}
    (cursor rate : Nat) (hr : 0 < rate)
    {suffix : UInt8}
    (hbytes : Bytes t.external pointer 200 (fun i ↦
      (memByte s.external (pointer + BitVec.ofNat 64 i) ^^^
        (if i = cursor then suffix else 0)) ^^^ (if i + 1 = rate then 0x80 else 0))) :
    Permutation.memoryLanes pointer t = fun lane ↦
      (Permutation.memoryLanes pointer s lane ^^^ Incremental.byteLanes cursor suffix lane) ^^^
        Incremental.byteLanes (rate - 1) 0x80 lane := by
  apply padded_state_eq _ cursor rate hr _ _ hbytes
  intro lane j
  exact (LaneMemory.storedByte_memoryLanes pointer s lane j).symm

end Sha3.Proofs.Finalize.Padding
