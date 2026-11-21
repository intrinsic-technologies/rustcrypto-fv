import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.State
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Memory
import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.Verifying.Message.Hash.Short.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial start s : RamState}
    {secret message : ByteArray} (pre : HashEntry initial start secret message)
    (copied : Copied initial start s message) (short : message.size < 64) :
    ∃ t, Result initial start t message := by
  have hp : Tail.Pre s := by
    refine ⟨copied.rip, ?_, ?_⟩
    · have hw := stack_writable pre.context copied.toFrame
        (offset := 239) (len := 1) (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · intro pc len bound
      exact stack_code pre.context copied.toFrame
        (offset := 239) (len := 1) (by decide) bound
  obtain ⟨fuelU, u, runU, readyU, _, effect⟩ := Tail.run (returnBoundary initial) (outside pre.context) s
    (readyToStep copied.machine copied.bindingsSupported) (Tail.code copied.loaded) hp
  have stateU := tail_frame pre.context copied.toFrame runU readyU effect
  have rsp : stackPtr s = frameBase initial := copied.rsp
  have bytes (offset len : Nat) (bound : offset + len < 2^64)
      (apart : offset + len ≤ 239 ∨ 240 ≤ offset) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    simpa only [rsp] using tail_byte effect bound apart hi
  have stores : memLoad u.external (stackPtr s + 239) 8 = BitVec.ofNat 8 message.size := by
    have h := effect.writes
    change memLoad u.external (stackPtr s + 239) 8 = (s.regValue .rbp).setWidth 8 at h
    rw [copied.length] at h
    simpa only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] using h
  have position : u.external[frameBase initial + 239]? = some (UInt8.ofNat message.size) := by
    have writable := hp.writable
    have readable : MemReadable s (stackPtr s + 239) 1 := ⟨writable.low, writable.mem⟩
    have alloc := readable.of_holds effect
    have raw := Bytes.of_memLoad (n := 8) alloc.mem
    change Bytes u.external (stackPtr s + 239) 1
      (storedByte (memLoad u.external (stackPtr s + 239) 8)) at raw
    rw [stores] at raw
    have h := raw 0 (by decide)
    have byte : storedByte (BitVec.ofNat 8 message.size) 0 = UInt8.ofNat message.size := by
      simp only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : message.size < 2^8)]
    simpa only [rsp, BitVec.ofNat_eq_ofNat, BitVec.add_zero, byte] using h
  have buffer : (MemoryRegion.mk (frameBase initial + 176).toNat message.size).HasBytes
      u.external message := by
    exact hasBytes_copy copied.buffer (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 176 message.size (by omega) (.inl (by omega)) i hi)
  have hash : SHA256.HashStateAt u (frameBase initial + 240) SHA256.initialHash := by
    exact SHA256.HashStateAt.copy copied.hash (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 240 32 (by decide) (.inr (by decide)) i hi)
  have count : loadBytes u.external (frameBase initial + 272) 8 = .ok (0#64) := by
    apply loadBytes_ok_copy _ copied.count
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat] using bytes 272 8 (by decide) (.inr (by decide)) i hi
  have stateHash : HMAC.Sha256StateAt u (frameBase initial + 176) message := by
    apply P256.Proofs.Verifying.Message.Hash.Short.small_state short buffer
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using position
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hash
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using count
  exact ⟨u, stateU, effect.rip, stateHash⟩

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short
