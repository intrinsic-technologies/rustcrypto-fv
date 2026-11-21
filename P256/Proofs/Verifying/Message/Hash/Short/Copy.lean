import P256.Proofs.Verifying.Message.Hash.Short.Prepare
import P256.Proofs.Verifying.Message.Hash.Short.State
import P256.Proofs.Verifying.Message.Hash.Long.Copy
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary) (ready : Ready initial s t boundary message)
    (short : message.size < 64) : ∃ u, Copied initial u boundary message := by
  have memory : MemoryWriteFrame initial t #v[Stack.region initial 9992] := by
    intro a outside
    rw [ready.memory]
    exact initialized.stackFrame a outside
  have destination : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 704 := by
    rw [ready.destination]
    simp only [frameBase]
    bv_omega
  obtain ⟨u, result⟩ := Long.Copy.copy (sourceOffset := 0) (count := message.size)
    (outputOffset := 704) pre ready.toFrameState memory (by omega) (by decide) (by omega)
    0xd621 0xf6ed1 (by decide) (by decide +kernel) (by decide) ready.rip
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ready.source)
    destination ready.count
  have bytes (offset len : Nat) (bound : offset + len ≤ 1176)
      (apart : offset + len ≤ 472 ∨ 472 + message.size ≤ offset) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    have h := result.stack_byte pre (offset := 1176-offset) (len := len)
      (by decide) (by omega) (by omega) (by omega) hi
    have addr : stackPtr initial - BitVec.ofNat 64 (1176-offset) =
        frameBase initial + BitVec.ofNat 64 offset := by
      simp only [frameBase]
      bv_omega
    simpa only [addr, ready.memory] using h
  have words := initialized.hash.hash
  have blocks := initialized.hash.count
  have words' : SHA256.HashStateAt s (frameBase initial + 536) SHA256.initialHash := by
    have h : SHA256.HashStateAt s (frameBase initial + 472 + 64) SHA256.initialHash := words
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have blocks' : loadBytes s.external (frameBase initial + 568) 8 = .ok (0#64) := by
    have h : loadBytes s.external (frameBase initial + 472 + 96) 8 = .ok (0#64) := blocks
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have saved (offset : Nat) (bound : offset + 8 ≤ 472) :
      memLoad u.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun b : Option UInt8 => b.getD 0) (bytes offset 8 (by omega) (.inl bound) i hi)
  have savedWords := initialized_saved initialized
  have sourceBytes : (messageRegion initial message).HasBytes t.external message :=
    frame_hasBytes memory (by
      intro region member
      have eq : region = Stack.region initial 9992 := by simpa using member
      simpa only [eq] using pre.messageStack) pre.messageBounded pre.messageBytes
  refine ⟨u, result.toFrameState, ?_, ?_,
    (result.calleeSaved .r13 (by decide)).trans ready.current,
    (result.calleeSaved .r12 (by decide)).trans ready.endPointer,
    (result.calleeSaved .rbx (by decide)).trans ready.position,
    (result.calleeSaved .r15 (by decide)).trans ready.length, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨before, runBefore⟩ := ready.execution
    obtain ⟨fuel, run⟩ := result.execution
    exact ⟨before + fuel, runBefore.trans run⟩
  · exact result.rip
  · apply hasBytes_copy sourceBytes
    intro i hi
    have h := result.copied i hi
    have addr : stackPtr initial - BitVec.ofNat 64 704 = frameBase initial + 472 := by
      simp only [frameBase]
      bv_omega
    simpa only [addr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · exact SHA256.HashStateAt.copy words' (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 536 32 (by decide) (.inr (by omega)) i hi)
  · apply loadBytes_ok_copy _ blocks'
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat] using bytes 568 8 (by decide) (.inr (by omega)) i hi
  · have h : memLoad u.external (frameBase initial + 456) 64 =
        memLoad s.external (frameBase initial + 456) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 456 (by decide)
    exact h.trans savedWords.1
  · have h : memLoad u.external (frameBase initial + 384) 64 =
        memLoad s.external (frameBase initial + 384) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 384 (by decide)
    exact h.trans savedWords.2.1
  · have h : memLoad u.external (frameBase initial + 464) 64 =
        memLoad s.external (frameBase initial + 464) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using saved 464 (by decide)
    exact h.trans savedWords.2.2
  · exact memoryWriteFrame_trans memory (work_frame_stack pre.toCalleePre result.writes)

end P256.Proofs.Verifying.Message.Hash.Short
