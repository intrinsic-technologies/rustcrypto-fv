import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.Nonce.Update.Seeded.Absorb.CrossPrepare
import P256.Proofs.Nonce.Update.Seeded.Absorb.Memory
import P256.Proofs.Nonce.Update.Seeded.Absorb.SeedCopy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb
open Update.Absorb.Seeded (copy_scratch_byte)

structure CrossCopied [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray)
    (address : BitVec 64) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a7c0
  current : s.regValue .rbp = initial.regValue .rsi
  outer : (MemoryRegion.mk (scratch initial + 256).toNat 64).HasBytes s.external (HMAC.keyPad state.key 0x5c)
  hash : SHA256.HashStateAt s (scratch initial + 384)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input))
  count : loadBytes s.external (scratch initial + 416) 8 = .ok (1 : BitVec 64)
  block : (MemoryRegion.mk (scratch initial + 320).toNat 64).HasBytes s.external (input ++ secret.extract 0 31)
  tail : s.regValue .rbx = address + 31
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  remaining : s.regValue .r15 = 1

set_option maxHeartbeats 1000000 in
theorem copy_cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (ready : CrossReady initial s state input address)
    (inputSize : input.size = 33) (secretSize : secret.size = 32)
    (seed : UpdateSeedAt initial address secret) :
    ∃ fuel t, Advances boundary fuel s t ∧ CrossCopied initial t state input secret address := by
  obtain ⟨t,result⟩ := copy_seed (sourceOffset := 0) (count := 31) (outputOffset := 327)
    pre ready.toFrameState (Or.inr ⟨secret, seed, by omega⟩) (by decide) (by decide) (by decide)
    0xa7bd (by decide) (by decide +kernel) ready.copyPointer ready.rip
    (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using ready.source)
    (ready.destination.trans (by simp only [scratch]; bv_omega)) ready.count
  have ctx := ready.toContext.after_copy pre result (by decide)
  have kept (offset len : Nat) (bound : offset ≤ 680) (span : offset+len ≤ 688)
      (apart : offset+len ≤ 353 ∨ 384 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact copy_scratch_byte pre result (by decide) bound span (by omega) hi
  have original : (MemoryRegion.mk (scratch initial + 320).toNat input.size).HasBytes s.external input := by
    have h := ready.hmac.inner.buffer
    rw [ByteArray.size_append,HMAC.keyPad_size,inputSize] at h
    simpa only [inputSize,Nat.reduceMod,HMAC.remainderBytes_keyPad_append,
      HMAC.remainderBytes_short input (by omega),BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
  have firstBytes : (MemoryRegion.mk (scratch initial + 320).toNat input.size).HasBytes t.external input :=
    P256.Proofs.Program.hasBytes_copy original (kept 320 input.size (by decide) (by omega) (by omega))
  have extractedSize : (secret.extract 0 31).size = 31 := by
    rw [ByteArray.size_extract,secretSize]; decide
  have source : (MemoryRegion.mk address.toNat (secret.extract 0 31).size).HasBytes s.external (secret.extract 0 31) := by
    have h := hasBytes_extract (P256.Proofs.Program.hasBytes_copy seed.contents (seed_bytes ready.toFrameState seed)) 0 31
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  have added : (MemoryRegion.mk (scratch initial + 353).toNat (secret.extract 0 31).size).HasBytes t.external (secret.extract 0 31) := by
    apply P256.Proofs.Program.hasBytes_copy source
    intro i hi
    rw [extractedSize] at hi
    have h := result.copied i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,
      show stackPtr initial - 327#64 = scratch initial + 353#64 by simp only [scratch]; bv_omega] using h
  have block := hasBytes_append (first := input) (second := secret.extract 0 31) firstBytes (by
    simpa only [inputSize,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using added)
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨fuel,t,run,ctx,result.rip,
    (result.calleeSaved .rbp (by decide +kernel)).trans ready.current,
    P256.Proofs.Program.hasBytes_copy ready.hmac.outer (kept 256 64 (by decide) (by decide) (by decide)),?_,?_,?_,
    (result.calleeSaved .rbx (by decide +kernel)).trans ready.tail,
    (result.calleeSaved .r14 (by decide +kernel)).trans ready.hashPointer,
    (result.calleeSaved .r13 (by decide +kernel)).trans ready.copyPointer,
    (result.calleeSaved .r15 (by decide +kernel)).trans ready.remaining⟩
  · apply SHA256.HashStateAt.copy (by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using ready.hmac.inner.hash)
    exact kept 384 32 (by decide) (by decide) (by decide)
  · apply P256.Proofs.Program.loadBytes_ok_copy (kept 416 8 (by decide) (by decide) (by decide))
    simpa only [ByteArray.size_append,HMAC.keyPad_size,inputSize,Nat.reduceAdd,Nat.reduceDiv,
      BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using ready.hmac.inner.count
  · simpa only [ByteArray.size_append,inputSize,extractedSize] using block

end P256.Proofs.Nonce.Update.Seeded.Absorb
