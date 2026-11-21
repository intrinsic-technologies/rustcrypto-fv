import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.HMAC.Key.Output
open X86 X86.Machine X86.UserProcess X86Proofs

theorem bytes_of_words {s t : RamState} {source destination : BitVec 64} {count : Nat}
    (readable : MemReadable s source (8 * count))
    (allocated : MemReadable t destination (8 * count))
    (words : ∀ j < count,
      memLoad t.external (destination + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (source + BitVec.ofNat 64 (8*j)) 64) :
    ∀ i < 8 * count, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]? := by
  intro i hi
  have src := Bytes.of_memLoad (n := 64) (a := source + BitVec.ofNat 64 (8*(i/8)))
    (m := s.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem (8*(i/8)+j) (by omega))
  have dst := Bytes.of_memLoad (n := 64) (a := destination + BitVec.ofNat 64 (8*(i/8)))
    (m := t.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated.mem (8*(i/8)+j) (by omega))
  rw [words (i/8) (by omega)] at dst
  have eq := (dst (i%8) (by omega)).trans (src (i%8) (by omega)).symm
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using eq

end P256.Proofs.HMAC.Key.Output
