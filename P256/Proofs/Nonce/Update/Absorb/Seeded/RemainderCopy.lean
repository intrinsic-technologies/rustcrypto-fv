import P256.Proofs.Nonce.Update.Absorb.Seeded.Digest

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure CrossDone [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a37d
  current : s.regValue .r14 = initial.regValue .rsi
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input

set_option maxHeartbeats 1000000 in
theorem copy_remainder [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (ready : RemainderReady initial s state input secret address)
    (inputSize : input.size = 33) (secretSize : secret.size = 32)
    (seed : UpdateSeedAt initial address secret) :
    ∃ fuel t, Advances boundary fuel s t ∧ CrossDone initial t state (input ++ secret) := by
  obtain ⟨t,result⟩ := copy_seed (sourceOffset := 31) (count := 1) (outputOffset := 528)
    pre ready.toFrameState seed (by omega) (by decide) (by decide) (by decide)
    0xa377 0xfa17b (by decide) (by decide +kernel) (by decide) ready.rip ready.source
    (ready.destination.trans (by simp only [scratch]; bv_omega)) ready.countRegister
  have ctx := ready.toContext.after_copy pre result (by decide) (by decide)
  have kept (offset len : Nat) (bound : offset ≤ 680) (span : offset+len ≤ 688)
      (apart : offset+len ≤ 152 ∨ 153 ≤ offset) :
      ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact copy_scratch_byte pre result (by decide) bound span (by omega) hi
  have digest := ready.toDigest.after ctx (result.calleeSaved .r14 (by decide +kernel))
    (kept 88 64 (by decide) (by decide) (by decide))
    (kept 216 40 (by decide) (by decide) (by decide))
  have position : t.external[scratch initial + 215]? = some 1 := by
    have h := kept 215 1 (by decide) (by decide) (by decide) 0 (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans ready.position
  have extractedSize : (secret.extract 31 32).size = 1 := by
    rw [ByteArray.size_extract,secretSize]; decide
  have source : (MemoryRegion.mk (address + 31).toNat 1).HasBytes s.external (secret.extract 31 32) := by
    have h := hasBytes_extract (P256.Proofs.Program.hasBytes_copy seed.contents (seed_bytes ready.toFrameState seed)) 31 32
    simpa only [extractedSize,BitVec.ofNat_eq_ofNat] using h
  have buffer : (MemoryRegion.mk (scratch initial + 152).toNat 1).HasBytes t.external (secret.extract 31 32) := by
    apply P256.Proofs.Program.hasBytes_copy source
    intro i hi
    have h := result.copied i hi
    simpa only [BitVec.ofNat_eq_ofNat,
      show stackPtr initial - 528#64 = scratch initial + 152#64 by simp only [scratch]; bv_omega] using h
  obtain ⟨fuel,run⟩ := result.execution
  exact ⟨fuel,t,run,ctx,result.rip,digest.current,digest.hmac inputSize secretSize buffer position⟩

end P256.Proofs.Nonce.Update.Absorb.Seeded
