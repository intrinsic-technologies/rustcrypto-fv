import Sha1.Proofs.Buffered.Finalize.Digest.BlocksDigest
import Sha1.Proofs.Buffered.Finalize.Geometry

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST

abbrev savedOutput (s : RamState) := (Operand.mem (stackPtr s + 0xc0) : Operand 64).read s

structure Run [Bindings] (boundary : ReturnBoundary) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rsp : stackPtr t = stackPtr s
  saved : savedOutput t = savedOutput s
  agrees : AgreesExcept (Kind.updateFinalizeCopy.changes s) s t

theorem Run.trans [Bindings] {b : ReturnBoundary} {s t u : RamState}
    (h : Run b s t) (k : Run b t u) : Run b s u := by
  obtain ⟨i, hi⟩ := h.advances
  obtain ⟨j, hj⟩ := k.advances
  have he : Kind.updateFinalizeCopy.changes t = Kind.updateFinalizeCopy.changes s := by
    have hs := h.saved
    unfold savedOutput at hs
    rw [h.rsp] at hs
    simp only [Kind.changes, Kind.localChanges, hs, h.rsp]
  refine ⟨⟨i+j, hi.trans hj⟩, k.ready, k.code, k.rsp.trans h.rsp, k.saved.trans h.saved, ?_⟩
  have hk := k.agrees
  rw [he] at hk
  exact (h.agrees.trans hk).mono (by simp)

theorem stack_word_bytes {kind : Kind} {s t : RamState} (hs : Storage kind s)
    (ht : Storage kind t) (hsp : stackPtr t = stackPtr s) {src dst : Nat}
    (hsrc : src + 8 ≤ kind.stackBytes) (hdst : dst + 8 ≤ kind.stackBytes)
    (hword : (Operand.mem (stackPtr s + BitVec.ofNat 64 dst) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 src) : Operand 64).read s)
    (i : Nat) (hi : i < 8) :
    t.external[stackPtr s + BitVec.ofNat 64 dst + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 src + BitVec.ofNat 64 i]? := by
  change memLoad t.external _ 64 = memLoad s.external _ 64 at hword
  have hd := (ht.stackWritable dst 8 hdst).mem
  rw [hsp] at hd
  rw [Bytes.of_memLoad (n := 64) hd i hi,
    Bytes.of_memLoad (n := 64) (hs.stackWritable src 8 hsrc).mem i hi, ← hword]

abbrev StateBytes (s : RamState) (H : Vector (BitVec 32) 5) :=
  (⟨(stackPtr s + 8).toNat, 20⟩ : MemoryRegion).HasBytes s.external
    (Wrapper.Hash.Serialize.stateBytes H)

structure Position (m : ByteArray) (s : RamState) : Prop where
  position : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (m.size % 64)
  blocks : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (m.size / 64)

structure Prepared (m : ByteArray) (s : RamState) : Prop extends Position m s where
  rip : s.RIP = 0x101e0b
  df : DirectionFlagClear s.RFLAGS
  state : StateBytes s (absorbedHash m)
  tail : (⟨(stackPtr s + 32).toNat, (tailBytes m).size⟩ : MemoryRegion).HasBytes
    s.external (tailBytes m)

structure Padded (m : ByteArray) (s : RamState) : Prop extends Position m s where
  rip : s.RIP = if m.size % 64 < 56 then 0x101ef3 else 0x101e35
  df : DirectionFlagClear s.RFLAGS
  state : StateBytes s (absorbedHash m)
  padded : Bytes s.external (stackPtr s + 32) 64 (fun i ↦ (Digest.firstBlock m)[i]!)

def penultimateHash (m : ByteArray) : Vector (BitVec 32) 5 :=
  if m.size % 64 < 56 then absorbedHash m
  else Wrapper.Absorb.compressBlocks (absorbedHash m) (Digest.firstBlock m)

structure Last (m : ByteArray) (s : RamState) : Prop extends Position m s where
  rip : s.RIP = 0x101ef3
  df : DirectionFlagClear s.RFLAGS
  state : StateBytes s (penultimateHash m)
  prefixBytes : ∀ i < 56, s.external[stackPtr s + 32 + BitVec.ofNat 64 i]? =
    some (if m.size % 64 < 56 then (Digest.firstBlock m)[i]! else 0)

def finalHash (m : ByteArray) := Wrapper.Absorb.compressBlocks (penultimateHash m) (Digest.lastBlock m)

theorem resultBytes (m : ByteArray) : Kind.updateFinalizeCopy.resultBytes m =
    ⟨(SHA1.toDigest (finalHash m)).bytes.toArray⟩ := by
  change (⟨(SHA1.toDigest (SHA1.hashComputation (SHA2.SHA256.parse
    (SHA2.SHA256.pad (SHA2.bytesToBits m))))).bytes.toArray⟩ : ByteArray) = _
  rw [← Digest.bytesToBits_paddedMessage]
  change (⟨(SHA1.toDigest (Wrapper.Absorb.compressBlocks SHA1.initialHashValue
    (Digest.paddedMessage m))).bytes.toArray⟩ : ByteArray) = _
  by_cases h : m.size % 64 < 56
  · rw [Digest.paddedMessage_short m h, Wrapper.Absorb.compressBlocks_append _ _ _ (fullBytes_aligned m)]
    simp only [finalHash, penultimateHash, h, ite_true]
    rfl
  · rw [Digest.paddedMessage_long m (by omega), Wrapper.Absorb.compressBlocks_append _ _ _ (by
        rw [ByteArray.size_append, Digest.size_firstBlock, size_fullBytes]; omega),
        Wrapper.Absorb.compressBlocks_append _ _ _ (fullBytes_aligned m)]
    simp only [finalHash, penultimateHash, h, ite_false]
    rfl

end Sha1.Proofs.Buffered.Finalize.Family
