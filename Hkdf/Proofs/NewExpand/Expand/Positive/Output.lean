import Hkdf.Proofs.NewExpand.Expand.LoopState

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def outputChunk (entry : RamState) (length n : Nat) : MemoryRegion :=
  ⟨(entry.regValue .rcx).toNat + 32 * n, min (length - 32 * n) 32⟩

theorem roundOutput [Bindings] {entry s t : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (written : (registerRegion entry .rcx (min (32 * n) length)).HasBytes s.external
      ((blocks .sha256 key info n).1.extract 0 length)) (more : 32 * n < length)
    (bound : length ≤ 8160)
    (frame : MemoryWriteFrame s t #v[outputChunk entry length n, Stack.region entry 2264])
    (chunk : (outputChunk entry length n).HasBytes t.external
      ((blocks .sha256 key info (n + 1)).2.extract 0 (min (length - 32 * n) 32))) :
    (registerRegion entry .rcx (min (32 * (n + 1)) length)).HasBytes t.external
      ((blocks .sha256 key info (n + 1)).1.extract 0 length) := by
  have prevSize := blocks_sha256_size key info n
  have totalSize := blocks_sha256_size key info (n + 1)
  have digestSize := blocks_sha256_previous_size key info (count := n + 1) (by omega)
  have splitBlock : (blocks .sha256 key info (n + 1)).1 =
      (blocks .sha256 key info n).1 ++ (blocks .sha256 key info (n + 1)).2 := by
    rw [blocks_succ]
    rfl
  have outputBound := (pre.output (by omega) bound).1
  change (entry.regValue .rcx).toNat + length < 2^32 at outputBound
  have disjoint : (registerRegion entry .rcx length).Disjoint (Stack.region entry 2264) :=
    (pre.separation (by omega) bound).1 0 1 (by decide)
  refine ⟨?_, fun i => ?_⟩
  · change ((blocks .sha256 key info (n+1)).1.extract 0 length).size = _
    rw [ByteArray.size_extract, totalSize, Nat.sub_zero, Nat.min_comm]
    rfl
  rcases i with ⟨i, hi⟩
  change t.external[BitVec.ofNat 64 ((entry.regValue .rcx).toNat + i)]? = _
  rw [ByteArray.size_extract, Nat.sub_zero, totalSize] at hi
  have byteAddr : (BitVec.ofNat 64 ((entry.regValue .rcx).toNat + i)).toNat =
      (entry.regValue .rcx).toNat + i :=
    Nat.mod_eq_of_lt (by omega)
  by_cases old : i < 32 * n
  · have before : i < ((blocks .sha256 key info n).1.extract 0 length).size := by
      rw [ByteArray.size_extract, prevSize]; omega
    have kept := frame (BitVec.ofNat 64 ((entry.regValue .rcx).toNat + i)) (by
      intro region member
      have choices : region = outputChunk entry length n ∨ region = Stack.region entry 2264 := by
        simpa using member
      rcases choices with rfl | rfl
      · change ¬ ((entry.regValue .rcx).toNat + 32 * n ≤ _ ∧ _ < _)
        rw [byteAddr]
        omega
      · apply disjoint
        rw [byteAddr]
        change (entry.regValue .rcx).toNat ≤ (entry.regValue .rcx).toNat + i ∧
          (entry.regValue .rcx).toNat + i < (entry.regValue .rcx).toNat + length
        constructor <;> omega)
    have value := kept.trans (written.2 ⟨i, before⟩)
    have inPrev : i < (blocks .sha256 key info n).1.size := by omega
    simpa only [ByteArray.getElem_extract, Nat.zero_add, splitBlock,
      ByteArray.getElem_append_left inPrev] using value
  · let j := i - 32 * n
    have index : 32 * n + j = i := by dsimp only [j]; omega
    have hj : j < ((blocks .sha256 key info (n + 1)).2.extract 0 (min (length - 32 * n) 32)).size := by
      rw [ByteArray.size_extract, digestSize]
      dsimp only [j]
      omega
    have value := chunk.2 ⟨j, hj⟩
    change t.external[BitVec.ofNat 64 ((entry.regValue .rcx).toNat + 32 * n + j)]? = _ at value
    rw [Nat.add_assoc, index] at value
    have inDigest : (blocks .sha256 key info n).1.size ≤ i := by omega
    simpa only [ByteArray.getElem_extract, Nat.zero_add, splitBlock,
      ByteArray.getElem_append_right inDigest, prevSize, j] using value

end Hkdf.Proofs.NewExpand.Expand
