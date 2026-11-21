import P256.Proofs.Verifying.Message.Hash.Short.State
import P256.Proofs.Verifying.Message.Hash.Short.Memory
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (copied : Copied initial s boundary message) (short : message.size < 64) :
    ∃ t, Buffered initial t boundary message := by
  have hp : Tail.Pre s := by
    refine ⟨copied.rip, ?_, ?_⟩
    · have hw := ScalarFrame.stack_writable pre.toCalleePre copied.toFrameState
        (offset := 535) (len := 1) (by decide) (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · intro pc len bound
      exact ScalarFrame.stack_code pre.toCalleePre copied.toFrameState
        (offset := 535) (len := 1) (by decide) (by decide) bound
  obtain ⟨fuelU, u, runU, readyU, _, effect⟩ := Tail.run boundary pre.outerBoundary s
    (readyToStep copied.machine copied.bindingsSupported) (Tail.code copied.loaded) hp
  have stateU := tail_frame pre.toCalleePre copied.toFrameState readyU effect
  have memoryU := work_frame_stack pre.toCalleePre
    (effect.agrees.memoryWriteFrame (tail_writes pre.toCalleePre copied.toFrameState))
  have rsp : stackPtr s = frameBase initial := copied.rsp
  have bytes (offset len : Nat) (bound : offset + len < 2^64)
      (apart : offset + len ≤ 535 ∨ 536 ≤ offset) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    simpa only [rsp] using tail_byte effect bound apart hi
  have sum : Tail.sum s = BitVec.ofNat 8 message.size := by
    change (s.regValue .r15).setWidth 8 + (s.regValue .rbx).setWidth 8 = _
    rw [copied.length, copied.position]
    bv_omega
  have stores := effect.writes
  change u.regValue .r15 = _ ∧ memLoad u.external (stackPtr s + 535) 8 = Tail.sum s ∧
    u.regValue .r13 = s.regValue .r13 + 16 at stores
  have position : u.external[frameBase initial + 535]? = some (UInt8.ofNat message.size) := by
    have writable := hp.writable
    have readable : MemReadable s (stackPtr s + 535) 1 := ⟨writable.low, writable.mem⟩
    have alloc := readable.of_holds effect
    have raw := Bytes.of_memLoad (n := 8) alloc.mem
    change Bytes u.external (stackPtr s + 535) 1
      (storedByte (memLoad u.external (stackPtr s + 535) 8)) at raw
    rw [stores.2.1, sum] at raw
    have h := raw 0 (by decide)
    have byte : storedByte (BitVec.ofNat 8 message.size) 0 = UInt8.ofNat message.size := by
      simp only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : message.size < 2^8)]
    simpa only [rsp, BitVec.ofNat_eq_ofNat, BitVec.add_zero, byte] using h
  have buffer : (MemoryRegion.mk (frameBase initial + 472).toNat message.size).HasBytes
      u.external message := by
    exact hasBytes_copy copied.buffer (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 472 message.size (by omega) (.inl (by omega)) i hi)
  have hash : SHA256.HashStateAt u (frameBase initial + 536) SHA256.initialHash := by
    exact SHA256.HashStateAt.copy copied.hash (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 536 32 (by decide) (.inr (by decide)) i hi)
  have count : loadBytes u.external (frameBase initial + 568) 8 = .ok (0#64) := by
    apply loadBytes_ok_copy _ copied.count
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat] using bytes 568 8 (by decide) (.inr (by decide)) i hi
  have stateHash : HMAC.Sha256StateAt u (frameBase initial + 472) message := by
    apply small_state short buffer
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using position
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hash
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using count
  have saved (offset : Nat) (bound : offset + 8 ≤ 535) :
      memLoad u.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    simpa only [rsp] using tail_load effect (offset := offset) (width := 64) (by omega) (.inl bound)
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have h := effect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((s.regValue .r13 + 16) - s.regValue .r12) == 0) at h
    rw [copied.current, copied.endPointer] at h
    simpa only [BitVec.sub_self, BitVec.ofNat_eq_ofNat, beq_self_eq_true] using h
  obtain ⟨t, stepT, readyT, branchT⟩ := jcc_rel32_effect_step 0x10d639 4 0xde u readyU
    (programText_slice (programLoaded_codeIn stateU.loaded) 0xd639 _ (by decide) (by decide +kernel))
    ⟨effect.rip, by intro; decide⟩
  have ripT : t.RIP = 0x10d71d := by
    rw [branchT.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10d71d else 0x10d63f) = _
    rw [zero]
    rfl
  have runT : Advances boundary 1 u t := Advances.of_step stepT (.inl (by
    rw [ripT]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd71d (by decide))))
  have agreesT : AgreesExcept [.rip] u t := branchT.agrees
  have externalT := agreesT.external (by simp [Component.Covers])
  have stateT := stateU.after_registers readyT agreesT (by simp [Component.Covers]) (by simp)
  refine ⟨t, stateT, ?_, ripT, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨fuel, run⟩ := copied.execution
    exact ⟨fuel + fuelU + 1, (run.trans runU).trans runT⟩
  · exact stateHash.copy (fun _ _ => by rw [externalT])
  · rw [externalT]
    have h : memLoad u.external (frameBase initial + 456) 64 =
        memLoad s.external (frameBase initial + 456) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 456 (by decide)
    exact h.trans copied.savedKey
  · rw [externalT]
    have h : memLoad u.external (frameBase initial + 384) 64 =
        memLoad s.external (frameBase initial + 384) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 384 (by decide)
    exact h.trans copied.savedOutput
  · rw [externalT]
    have h : memLoad u.external (frameBase initial + 464) 64 =
        memLoad s.external (frameBase initial + 464) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 464 (by decide)
    exact h.trans copied.savedSignature
  · intro a outside
    rw [externalT]
    exact memoryWriteFrame_trans copied.stackFrame memoryU a outside

end P256.Proofs.Verifying.Message.Hash.Short
