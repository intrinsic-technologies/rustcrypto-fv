import P256.Proofs.Nonce.Update.Absorb.Seeded.CrossPrepare
import P256.Proofs.Nonce.Update.Absorb.Seeded.Memory
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure CrossCopied [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray)
    (address : BitVec 64) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a303
  current : s.regValue .r14 = initial.regValue .rsi
  outer : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external (HMAC.keyPad state.key 0x5c)
  hash : SHA256.HashStateAt s (scratch initial + 216)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input))
  count : loadBytes s.external (scratch initial + 248) 8 = .ok (1 : BitVec 64)
  block : (MemoryRegion.mk (scratch initial + 152).toNat 64).HasBytes s.external (input ++ secret.extract 0 31)
  tail : s.regValue .r15 = address + 31
  buffer : s.regValue .r13 = scratch initial + 152
  remaining : s.regValue .rbx = 1

set_option maxHeartbeats 1000000 in
theorem copy_cross [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (ready : CrossReady initial s state input address)
    (inputSize : input.size = 33) (secretSize : secret.size = 32)
    (seed : UpdateSeedAt initial address secret) :
    ∃ fuel t, Advances boundary fuel s t ∧ CrossCopied initial t state input secret address := by
  obtain ⟨t,result⟩ := copy_seed (sourceOffset := 0) (count := 31) (outputOffset := 495)
    pre ready.toFrameState seed (by omega) (by decide) (by decide) (by decide)
    0xa2fd 0xfa1f5 (by decide) (by decide +kernel) (by decide) ready.rip
    (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using ready.source)
    (ready.destination.trans (by simp only [scratch]; bv_omega)) ready.count
  have ctx := ready.toContext.after_copy pre result (by decide) (by decide)
  have kept (offset len : Nat) (bound : offset ≤ 680) (span : offset+len ≤ 688)
      (apart : offset+len ≤ 185 ∨ 216 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact copy_scratch_byte pre result (by decide) bound span (by omega) hi
  have original : (MemoryRegion.mk (scratch initial + 152).toNat input.size).HasBytes s.external input := by
    have h := ready.hmac.inner.buffer
    rw [ByteArray.size_append,HMAC.keyPad_size,inputSize] at h
    simpa only [inputSize,Nat.reduceMod,HMAC.remainderBytes_keyPad_append,
      HMAC.remainderBytes_short input (by omega),BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
  have firstBytes : (MemoryRegion.mk (scratch initial + 152).toNat input.size).HasBytes t.external input :=
    P256.Proofs.Program.hasBytes_copy original (kept 152 input.size (by decide) (by omega) (by omega))
  have extractedSize : (secret.extract 0 31).size = 31 := by
    rw [ByteArray.size_extract,secretSize]; decide
  have source : (MemoryRegion.mk address.toNat (secret.extract 0 31).size).HasBytes s.external (secret.extract 0 31) := by
    have h := hasBytes_extract (P256.Proofs.Program.hasBytes_copy seed.contents (seed_bytes ready.toFrameState seed)) 0 31
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  have added : (MemoryRegion.mk (scratch initial + 185).toNat (secret.extract 0 31).size).HasBytes t.external (secret.extract 0 31) := by
    apply P256.Proofs.Program.hasBytes_copy source
    intro i hi
    rw [extractedSize] at hi
    have h := result.copied i hi
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,
      show stackPtr initial - 495#64 = scratch initial + 185#64 by simp only [scratch]; bv_omega] using h
  have block := hasBytes_append (first := input) (second := secret.extract 0 31) firstBytes (by
    simpa only [inputSize,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using added)
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨fuel,t,run,ctx,result.rip,
    (result.calleeSaved .r14 (by decide +kernel)).trans ready.current,
    P256.Proofs.Program.hasBytes_copy ready.hmac.outer (kept 88 64 (by decide) (by decide) (by decide)),?_,?_,?_,
    (result.calleeSaved .r15 (by decide +kernel)).trans ready.tail,
    (result.calleeSaved .r13 (by decide +kernel)).trans ready.buffer,
    (result.calleeSaved .rbx (by decide +kernel)).trans ready.remaining⟩
  · apply SHA256.HashStateAt.copy (by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using ready.hmac.inner.hash)
    exact kept 216 32 (by decide) (by decide) (by decide)
  · apply P256.Proofs.Program.loadBytes_ok_copy (kept 248 8 (by decide) (by decide) (by decide))
    simpa only [ByteArray.size_append,HMAC.keyPad_size,inputSize,Nat.reduceAdd,Nat.reduceDiv,
      BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using ready.hmac.inner.count
  · simpa only [ByteArray.size_append,inputSize,extractedSize] using block

end P256.Proofs.Nonce.Update.Absorb.Seeded
