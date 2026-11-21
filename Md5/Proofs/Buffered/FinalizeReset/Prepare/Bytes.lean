import Md5.Proofs.Buffered.FinalizeReset.Prepare.Bytes.Frame

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_buffer {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (hp : Pre boundary message s variant) (hc : (copyEffect s variant).Holds s t) :
    (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
  have hsize := variant.stackBytes_bounds
  have hb : (⟨(stackPtr s + 0x48).toNat, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    have he : (context s).toNat + 64 = (stackPtr s + 0x48).toNat := by
      change (stackPtr s + BitVec.ofNat 64 8).toNat + 64 =
        (stackPtr s + BitVec.ofNat 64 72).toNat
      rw [Export.stackAddress_toNat hp.toStorage 8 (by omega),
        Export.stackAddress_toNat hp.toStorage 72 (by omega)]
    simpa only [he] using hp.absorbed.buffer
  have hw := hc.writes
  simp only [copyEffect, Write.AllHold] at hw
  apply Export.hasBytes_of_halves (bytes := (absorbedBuffer message).toBytes)
    (fun i hi ↦ hc.agrees.grow _ ((Export.stackWritable hp.toStorage 232 16
      (by omega)).bytes i hi)) hw.2.2.2.2
    (by simpa [BitVec.add_assoc] using hw.2.2.2.1)
  · intro i
    simpa using Export.digest_half hb 0 (by decide) i
  · intro i
    simpa [BitVec.add_assoc] using Export.digest_half hb 8 (by decide) i

theorem result_of_effects {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s u v t : RamState} (hp : Pre boundary message s variant)
    (hc : (copyEffect s variant).Holds s u) (hs : (setupEffect u variant).Holds u v)
    (ha : ∃ fuel, Advances boundary fuel s v)
    (hm : MemsetSiteResult boundary (variant.address 0x1007e6) v t) : Result boundary message s t variant := by
  have hsize := variant.stackBytes_bounds
  have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hup : (.reg 15 : Operand 64).read u = BitVec.ofNat 64 (message.size % 64) :=
    hc.writes.1.trans (position_eq hp)
  have husp := copy_rsp hc
  have hvsp : stackPtr v = stackPtr s := (setup_rsp hs).trans husp
  have hdi : rdi.read v = stackPtr s + BitVec.ofNat 64 (message.size % 64 + 9) := by
    rw [hs.writes.2.2.1, hup, husp]
    change stackPtr s + BitVec.ofNat 64 (message.size % 64) + BitVec.ofNat 64 9 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hdx : MemoryRoutines.rdx.read v = BitVec.ofNat 64 (63 - message.size % 64) := by
    rw [hs.writes.2.2.2.2, hup, remainingBytes _ hn]
  have hlen : (MemoryRoutines.rdx.read v).toNat = 63 - message.size % 64 := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcopy := copy_agrees_prepare hc
  have hsetup := setup_agrees_prepare husp hup hn hs
  have hsv : AgreesExcept (prepareChanges s) s v :=
    (hcopy.trans hsetup).mono (by simp)
  have hvs := agrees_storage hp.toStorage (prepare_agrees_reset hsv)
  have hmem := memset_agrees_prepare hvsp hdi hlen hn hm
  have hst : AgreesExcept (prepareChanges s) s t := (hsv.trans hmem).mono (by simp)
  have hreset := prepare_agrees_reset hst
  have hposition : (.reg 15 : Operand 64).read t =
      BitVec.ofNat 64 (message.size % 64) := by
    rw [hm.agrees.read (n := 64) (r := 15) (by simp [callSiteChanges]),
      hs.agrees.read (n := 64) (r := 15) (by
        simp [setupEffect, Effect.components, Write.component, Operand.component]), hup]
  have hremaining : (.reg 3 : Operand 64).read t =
      BitVec.ofNat 64 (63 - message.size % 64) := by
    rw [hm.agrees.read (n := 64) (r := 3) (by simp [callSiteChanges]),
      hs.writes.1, hup, remainingBytes _ hn]
  have hcopied : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    have hb := Block.bytes_of_hasBytes (copy_buffer hp hc)
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.size,
      Vector.size_toArray] at hb
    suffices hh : Bytes t.external (stackPtr s + 0xe8)
        (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size
        (fun i ↦ (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray)[i]!) by
      simpa only [ByteArray.size, Vector.size_toArray] using Finalize.hasBytes_of_bytes hh
    intro i hi
    have hi16 : i < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using hi
    have hmu := memset_byte hvs hvsp hdi hlen hn hm (232 + i) (by omega) (by omega)
    have hsu := setup_byte hup hn hs (232 + i) (by omega) (by omega)
    rw [husp] at hsu
    have he : stackPtr s + 0xe8 + BitVec.ofNat 64 i =
        stackPtr s + BitVec.ofNat 64 (232 + i) := by
      change stackPtr s + BitVec.ofNat 64 232 + BitVec.ofNat 64 i = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [← he] at hmu hsu
    exact hmu.trans (hsu.trans (hb i hi16))
  have hpadded : (⟨(context s).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      (firstBlock message) := by
    have htail := Block.bytes_of_hasBytes hp.absorbed.tail
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size_tailBytes] at htail
    have hbytes : Bytes t.external (context s) 64
        (fun i ↦ (firstBlock message)[i]!) := by
      apply Finalize.firstBlock_bytes
      · intro i hi
        have hmu := memset_byte hvs hvsp hdi hlen hn hm (8 + i) (by omega) (by omega)
        have hsu := setup_byte hup hn hs (8 + i) (by omega) (by omega)
        rw [husp] at hsu
        have hcu := copy_byte hc (8 + i) (by omega) (by omega)
        have he : context s + BitVec.ofNat 64 i =
            stackPtr s + BitVec.ofNat 64 (8 + i) := by
          change stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i = _
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        rw [← he] at hmu hsu hcu
        exact hmu.trans (hsu.trans (hcu.trans (htail i hi)))
      · have hmarker := hs.writes.2.1
        change (Operand.mem (stackPtr u + (.reg 15 : Operand 64).read u + 8) :
          Operand 8).read v = 128 at hmarker
        rw [hup, husp] at hmarker
        have haddr : stackPtr s + BitVec.ofNat 64 (message.size % 64) + 8 =
            context s + BitVec.ofNat 64 (message.size % 64) := by
          simp only [context, BitVec.add_assoc]
          rw [BitVec.add_comm (BitVec.ofNat 64 (message.size % 64))]
        rw [haddr] at hmarker
        have hall : ∀ i < 1,
            (v.external[context s + BitVec.ofNat 64 (message.size % 64) +
              BitVec.ofNat 64 i]?).isSome := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          simp only [BitVec.add_zero]
          apply hsv.grow
          have hh := (Export.stackWritable hp.toStorage (8 + message.size % 64) 1
            (by omega)).bytes 0 (by decide)
          simpa [context, BitVec.ofNat_add, BitVec.add_assoc] using hh
        have hbyte := Bytes.of_memLoad (n := 8) hall
        change memLoad v.external _ 8 = 128 at hmarker
        rw [hmarker] at hbyte
        have hzero := hbyte 0 (by decide)
        simp only [BitVec.add_zero] at hzero
        have hmu := memset_byte hvs hvsp hdi hlen hn hm (8 + message.size % 64)
          (by omega) (by omega)
        have he : context s + BitVec.ofNat 64 (message.size % 64) =
            stackPtr s + BitVec.ofNat 64 (8 + message.size % 64) := by
          change stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (message.size % 64) = _
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        rw [← he] at hmu
        exact hmu.trans hzero
      · intro i hi hilt
        have hf := hm.fill (i - (message.size % 64 + 1)) (by rw [hlen]; omega)
        rw [hdi, hs.writes.2.2.2.1] at hf
        have he : stackPtr s + BitVec.ofNat 64 (message.size % 64 + 9) +
            BitVec.ofNat 64 (i - (message.size % 64 + 1)) =
            context s + BitVec.ofNat 64 i := by
          change stackPtr s + BitVec.ofNat 64 (message.size % 64 + 9) +
            BitVec.ofNat 64 (i - (message.size % 64 + 1)) =
            stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i
          simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          omega
        rw [he] at hf
        exact hf
    have hh := Finalize.hasBytes_of_bytes (bytes := firstBlock message)
      (by rw [Finalize.size_firstBlock]; exact hbytes)
    simpa only [Finalize.size_firstBlock] using hh
  obtain ⟨f, hf⟩ := ha
  obtain ⟨g, hg⟩ := hm.advances
  exact ⟨⟨f + g, hf.trans hg⟩, hm.ready, hm.code, hm.rip,
    agrees_storage hp.toStorage hreset, hm.rsp.trans hvsp, hposition, hremaining,
    hcopied, hpadded, agrees_outputAddress hp.toStorage hreset, hst⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
