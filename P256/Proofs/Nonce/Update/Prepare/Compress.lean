import P256.Proofs.Nonce.Update.Prepare.CompressionMemory
import P256.Proofs.Nonce.Update.Prepare.CompressionState

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def compressionLayout : StackCallLayout 1856 64 32 336 :=
  ⟨688, 592, 360, by decide, by decide, by decide, by decide, by decide, by decide,
    .inl (by decide)⟩

set_option maxHeartbeats 600000 in
theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : CompressionInput initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t state := by
  have address (offset : Nat) (bound : offset ≤ 680) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) := by
    rw [← show stackPtr s = scratch initial from input.rsp]
    exact ScalarFrame.scalar_stack_address input.rsp (by decide) bound
  have addr151 : scratch initial + 319#64 = stackPtr initial - 361#64 := address 319 (by decide)
  have addr152 : scratch initial + 320#64 = stackPtr initial - 360#64 := address 320 (by decide)
  have addr184 : scratch initial + 352#64 = stackPtr initial - 328#64 := address 352 (by decide)
  have addr256 : scratch initial + 88#64 = stackPtr initial - 592#64 := address 88 (by decide)
  have destination : s.regValue .rdi = stackPtr initial - 360#64 := by
    simpa only [addr152, compressionLayout, BitVec.ofNat_eq_ofNat] using input.destination
  have source : s.regValue .rsi = stackPtr initial - 592#64 := by
    simpa only [addr256, compressionLayout, BitVec.ofNat_eq_ofNat] using input.source
  obtain ⟨t, result⟩ := compression_call pre input.toFrameState compressionLayout
    rfl (by decide) (by decide) 0xa05c 0xb92f (by decide)
    (by decide +kernel) (by decide +kernel) input.rip source destination input.count
    (by simpa only [addr256, compressionLayout, BitVec.ofNat_eq_ofNat] using input.key)
    (by simpa only [addr152, compressionLayout, BitVec.ofNat_eq_ofNat] using input.hash)
  have context : Context initial t state := ⟨result.toFrameState,
    (result.calleeSaved .rbx (by simp)).trans input.drbgPointer,
    (result.calleeSaved .rbp (by simp)).trans input.descriptors,
    (result.calleeSaved .r13 (by simp)).trans input.inputCount, input.drbg.copy result.drbg⟩
  have copied {offset len : Nat} (bound : offset ≤ 680) (span : len ≤ offset+8)
      (apart : 360 + len ≤ offset ∨ offset + 32 ≤ 360) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    fun _ hi => result.stack_byte pre (by decide) (by decide) bound span apart hi
  have position : t.external[scratch initial + 319#64]? = some 0 := by
    rw [addr151]
    have h := copied (offset := 361) (len := 1) (by decide) (by decide) (.inl (by decide)) 0 (by decide)
    simp only [BitVec.add_zero] at h
    exact h.trans (by simpa only [addr151, compressionLayout, BitVec.ofNat_eq_ofNat] using input.position)
  have blocks : loadBytes t.external (scratch initial + 352#64) 8 = .ok 1#64 := by
    rw [addr184]
    apply loadBytes_ok_copy (copied (by decide) (by decide) (.inr (by decide)))
    simpa only [addr184, compressionLayout, BitVec.ofNat_eq_ofNat] using input.blocks
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨fuel, t, run, context, result.rip, ?_, ?_⟩
  · apply hasBytes_copy input.key
    simpa only [addr256, compressionLayout, BitVec.ofNat_eq_ofNat] using
      copied (offset := 592) (len := 64) (by decide) (by decide) (.inl (by decide))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨SHA256.remainderBytes_size _, ?_⟩
      intro i
      have bound := i.isLt
      simp only [SHA256.remainderBytes_size, HMAC.keyPad_size, Nat.reduceMod] at bound
      exact (Nat.not_lt_zero _ bound).elim
    · simpa only [HMAC.keyPad_size, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd, UInt8.reduceOfNat] using position
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, addr152, compressionLayout, BitVec.ofNat_eq_ofNat] using result.hash
    · simpa only [HMAC.keyPad_size, Nat.reduceDiv, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using blocks

end P256.Proofs.Nonce.Update.Prepare
