import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Interface
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Copy
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Input
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Ready initial start s message) :
    ∃ t, Result initial start t message := by
  have destination : s.regValue .rdi = stackPtr initial - 344 := by
    rw [state.destination]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨u, copied⟩ := Copy.copy pre state.toFrame
    (sourceOffset := 64 * (message.size / 64)) (count := message.size % 64)
    (outputOffset := 344) (by omega) (by decide) (by omega)
    0x2846 0x101cac (by decide) (by decide +kernel) (by decide)
    state.rip (by rw [state.source, pre.pointer]) destination state.length
  have kept {offset len : Nat} (bound : offset ≤ 520) (span : len ≤ offset + 8)
      (apart : 344 + len ≤ offset ∨ offset + message.size % 64 ≤ 344)
      {i : Nat} (hi : i < len) :=
    copied.stack_byte pre (by decide) bound span apart hi
  have hashU : HMAC.Sha256StateAt u (frameBase initial + 176) message := by
    constructor
    · have slice := (message_slice pre state.toFrame
        (offset := 64 * (message.size / 64)) (count := message.size % 64) (by omega)).2.2
      have total : 64 * (message.size / 64) + message.size % 64 = message.size := by omega
      rw [total] at slice
      change (MemoryRegion.mk (memLoad initial.external (initial.regValue .rdi + 8) 64 +
        BitVec.ofNat 64 (64 * (message.size / 64))).toNat (message.size % 64)).HasBytes
        s.external (SHA256.remainderBytes message) at slice
      have result := hasBytes_copy slice copied.copied
      have address : frameBase initial + 176 = stackPtr initial - 344 := by
        simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [address]
      exact result
    · have h := kept (offset := 281) (len := 1) (by decide) (by decide) (.inr (by omega))
        (i := 0) (by decide)
      simp only [BitVec.add_zero] at h
      change u.external[stackPtr initial - 281]? = s.external[stackPtr initial - 281]? at h
      have pos : u.external[frameBase initial + 239]? = some (UInt8.ofNat (message.size % 64)) := by
        have addr : frameBase initial + 239 = stackPtr initial - 281 := by
          simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          rfl
        rw [← addr] at h
        exact h.trans state.position
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact pos
    · have hash : SHA256.HashStateAt s (stackPtr initial - 280)
          (SHA256.compressBlocks SHA256.initialHash message) := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.hash
      have out := hash.copy (fun i hi => kept (offset := 280) (len := 32)
        (by decide) (by decide) (.inr (by omega)) hi)
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using out
    · have count : loadBytes s.external (stackPtr initial - 248) 8 =
          .ok (BitVec.ofNat 64 (message.size / 64)) := by
        simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd] using state.count
      have out := loadBytes_ok_copy (fun i hi => kept (offset := 248) (len := 8)
        (by decide) (by decide) (.inr (by omega)) hi) count
      simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using out
  exact ⟨u, copied.toFrame, copied.rip, hashU⟩

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail
