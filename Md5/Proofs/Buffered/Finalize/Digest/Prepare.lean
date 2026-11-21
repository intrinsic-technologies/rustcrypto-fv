import Md5.Proofs.Buffered.Finalize.Digest.Copy
import Md5.Proofs.Buffered.Finalize.Digest.Normalize

namespace Md5.Proofs.Buffered.Finalize.Digest

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem Copied.rsp [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Copied boundary message s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [copyChanges])

theorem Copied.agreesDigest [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Copied boundary message s t) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro a c hc hcover
    simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (stackPtr s + 8) 168, by simp [Kind.changes, Kind.localChanges], ?_⟩
    exact FinalizeReset.Export.covers_shift (offset := 16) (len := 88)
      (by simpa [BitVec.add_assoc] using hcover) (by decide)

structure Prepared [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100100
  storage : Storage .digest t
  df : DirectionFlagClear t.RFLAGS
  rsp : stackPtr t = stackPtr s
  tail : (⟨(stackPtr t + 24).toNat, (tailBytes message).size⟩ : MemoryRegion).HasBytes
    t.external (tailBytes message)
  buffer : (⟨(stackPtr t + 8).toNat, 16⟩ : MemoryRegion).HasBytes
    t.external ⟨(absorbedBuffer message).toBytes.toArray⟩
  position : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  agrees : AgreesExcept (Kind.digest.changes s) s t

theorem prepare [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre .digest boundary message s) : ∃ t, Prepared boundary message s t := by
  obtain ⟨u, hu⟩ := copy_context hp
  obtain ⟨fuel, t, ht, hr, hc, he⟩ := Normalize.run hu.ready hu.code hp.boundaryOutside
    ⟨hu.storage, hu.rip, hu.state⟩
  have hsp : stackPtr t = stackPtr s := (Normalize.effect_rsp he).trans hu.rsp
  have hag : AgreesExcept (Kind.digest.changes s) s t := by
    have ha := Normalize.effect_agrees he
    have heq : Kind.digest.changes u = Kind.digest.changes s := by
      simp only [Kind.changes, Kind.localChanges, hu.rsp]
    rw [heq] at ha
    exact (hu.agreesDigest.trans ha).mono (by simp)
  have hb : (⟨(stackPtr u + 240).toNat, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    have hstart : (stackPtr u + 176).toNat + 64 = (stackPtr u + 240).toNat := by
      have h176 := hu.storage.stackAddress (offset := 176) (by decide)
      have h240 := hu.storage.stackAddress (offset := 240) (by decide)
      change (stackPtr u + BitVec.ofNat 64 176).toNat + 64 =
        (stackPtr u + BitVec.ofNat 64 240).toNat
      rw [h176, h240]
    exact hstart ▸ hu.source.buffer
  obtain ⟨n, ha⟩ := hu.advances
  exact ⟨t, ⟨⟨n + fuel, ha.trans ht⟩, hr, hc, he.rip,
    hu.storage.of_agrees he.agrees (Normalize.effect_rsp he),
    (hag.directionFlagClear
      (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges]) hp.df).df, hsp,
    Normalize.effect_tail he hu.absorbed,
    Normalize.effect_buffer hu.storage he hb, Normalize.effect_position he hu.absorbed,
    Normalize.effect_blocks he hu.absorbed, hag⟩⟩

end Md5.Proofs.Buffered.Finalize.Digest
