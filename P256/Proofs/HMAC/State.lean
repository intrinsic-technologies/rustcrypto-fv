import P256.Proofs.HMAC.Interface
import P256.Proofs.Program.CopyBytes
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem Sha256StateAt.copy {s t : RamState} {a b : BitVec 64} {input : ByteArray}
    (state : Sha256StateAt s a input)
    (copied : ∀ i < 104, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    Sha256StateAt t b input := by
  refine ⟨hasBytes_copy state.buffer (fun i hi => copied i (by omega)),
    (copied 63 (by decide)).trans state.position, ⟨state.hash.1, ?_⟩, ?_⟩
  · intro i hi
    apply loadBytes_ok_copy (source := s.external) (a := a + 64 + BitVec.ofNat 64 (4 * i)) _ (state.hash.2 i hi)
    have hc := copied_sub (offset := 64 + 4 * i) (len := 4) copied (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hc
  · exact loadBytes_ok_copy (copied_sub (offset := 96) (len := 8) copied (by decide)) state.count

theorem HmacStateAt.copy {s t : RamState} {a b : BitVec 64} {key input : ByteArray}
    (state : HmacStateAt s a key input)
    (copied : ∀ i < 168, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    HmacStateAt t b key input := by
  refine ⟨hasBytes_copy state.outer (fun i hi => copied i (by omega)), ?_⟩
  exact state.inner.copy (copied_sub (offset := 64) (len := 104) copied (by decide))

theorem Sha256StateAt.of_frame {s t : RamState} {a : BitVec 64} {input : ByteArray}
    {n : Nat} {regions : Vector MemoryRegion n}
    (state : Sha256StateAt s a input)
    (bounded : (MemoryRegion.mk a.toNat 104).Bounded)
    (frame : MemoryWriteFrame s t regions)
    (apart : ∀ region ∈ regions, (MemoryRegion.mk a.toNat 104).Disjoint region) :
    Sha256StateAt t a input := by
  apply state.copy
  intro i hi
  exact frame_read frame apart
    (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)

theorem HmacStateAt.of_frame {s t : RamState} {a : BitVec 64} {key input : ByteArray}
    {n : Nat} {regions : Vector MemoryRegion n}
    (state : HmacStateAt s a key input)
    (bounded : (MemoryRegion.mk a.toNat 168).Bounded)
    (frame : MemoryWriteFrame s t regions)
    (apart : ∀ region ∈ regions, (MemoryRegion.mk a.toNat 168).Disjoint region) :
    HmacStateAt t a key input := by
  apply state.copy
  intro i hi
  exact frame_read frame apart
    (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)

theorem sha256StateAt_keyPad_append {s : RamState} {a : BitVec 64} {key input : ByteArray}
    {pad : UInt8}
    (buffer : (MemoryRegion.mk a.toNat (input.size % 64)).HasBytes s.external
      (SHA256.remainderBytes input))
    (position : s.external[a + 63]? = some (UInt8.ofNat (input.size % 64)))
    (hash : SHA256.HashStateAt s (a + 64)
      (SHA256.compressBlocks
        (SHA256.Reference.compress SHA256.initialHash (Standards.NIST.SHA2.bytesToBits (keyPad key pad))) input))
    (count : loadBytes s.external (a + 96) 8 = .ok (BitVec.ofNat 64 (1 + input.size / 64))) :
    Sha256StateAt s a (keyPad key pad ++ input) := by
  have rem : (keyPad key pad ++ input).size % 64 = input.size % 64 := by
    rw [ByteArray.size_append, keyPad_size]
    omega
  have blocks : (keyPad key pad ++ input).size / 64 = 1 + input.size / 64 := by
    rw [ByteArray.size_append, keyPad_size]
    omega
  constructor
  · simpa only [rem, remainderBytes_keyPad_append] using buffer
  · simpa only [rem] using position
  · simpa only [compressBlocks_keyPad_append] using hash
  · simpa only [blocks] using count


end P256.Proofs.HMAC
