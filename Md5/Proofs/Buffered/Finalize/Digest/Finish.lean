import Md5.Proofs.Buffered.Finalize.Digest.Finish.Contracts
import Md5.Proofs.Buffered.Finalize.Digest.Finish.Length
import Md5.Proofs.Buffered.Finalize.Digest.Finish.Copy
import Md5.Proofs.Buffered.Finalize.Digest.Finish.Compression

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {buffer : Standards.RFC.MD5.Buffer} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x1001df)
    (hPosition : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hBlocks : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64))
    (hPrefix : Bytes s.external (stackPtr s + 24) 56
      (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0))
    (hBuffer : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) : ∃ t, Post boundary message buffer s t := by
  obtain ⟨n, u, hLength, huReady, huCode, hu⟩ :=
    Length.run hReady hCode hStorage hOutside hRip
  have hsu := Length.effect_rsp hu
  have huStorage := hStorage.of_agrees hu.agrees hsu
  have huPrefix : Bytes u.external (stackPtr u + 24) 56
      (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0) := by
    rw [hsu]
    exact Length.effect_prefix hu hPrefix
  have huBuffer : (⟨(stackPtr u + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩ := by
    rw [hsu]
    exact Length.effect_buffer hu hBuffer
  have huLength : Bytes u.external (stackPtr u + 168) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
    rw [hsu, ← Length.value_eq hPosition hBlocks]
    exact (Length.effect_lengths hStorage hu).2
  obtain ⟨m, v, hCopy, hvReady, hvCode, hv⟩ :=
    Copy.run huReady huCode huStorage hOutside hu.rip
  have hsv := Copy.effect_rsp hv
  have hvStorage := huStorage.of_agrees hv.agrees hsv
  have hvPrefix := Copy.effect_prefix huStorage hv huPrefix
  have hvLength : Bytes v.external (stackPtr u + 168) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
    exact Copy.effect_preserves hv huLength
      (RangeApart.offsets (stackPtr u) (by decide) (by decide) (Or.inl (by decide)))
  have hvBuffer : (⟨(stackPtr v + 8).toNat, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨buffer.toBytes.toArray⟩ := by
    rw [hsv]
    have hb := Block.bytes_of_hasBytes huBuffer
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    have hout := Copy.effect_preserves hv hb
      (RangeApart.offsets (stackPtr u) (by decide)
        (by simp [ByteArray.size]) (Or.inr (by simp [ByteArray.size])))
    simpa only [ByteArray.size, Vector.size_toArray] using hasBytes_of_bytes hout
  have hvInput : (⟨(stackPtr v + 112).toNat, 64⟩ : MemoryRegion).HasBytes
      v.external (lastBlock message) := by
    rw [hsv]
    have hl := lastBlock_bytes message hvPrefix (by
      simpa only [BitVec.add_assoc, show (112 : BitVec 64) + 56 = 168 from rfl]
        using hvLength)
    have hh := hasBytes_of_bytes (by rw [size_lastBlock]; exact hl)
    simpa only [size_lastBlock] using hh
  obtain ⟨hdi, hsi, hdx⟩ := Copy.effect_arguments hv
  have hdi' : v.regValue .rdi = stackPtr v + 8 := by
    rw [hsv]
    exact hdi
  have hsi' : v.regValue .rsi = stackPtr v + 112 := by
    rw [hsv]
    exact hsi
  obtain ⟨t, ht⟩ := Compression.run hvReady hvCode hvStorage hOutside hv.rip
    hdi' hsi' hdx hvInput hvBuffer
  have hCopyAgrees : AgreesExcept (Kind.digest.changes s) u v := by
    simpa only [Kind.changes, Kind.localChanges, hsu] using Copy.effect_agrees hv
  have hCompressAgrees : AgreesExcept (Kind.digest.changes s) v t := by
    simpa only [Kind.changes, Kind.localChanges, hsv, hsu] using
      Compression.agrees hdi' ht.agrees
  have hAgrees : AgreesExcept (Kind.digest.changes s) s t :=
    (((Length.effect_agrees hu).trans hCopyAgrees).trans hCompressAgrees).mono (by simp)
  obtain ⟨k, hCompress⟩ := ht.advances
  refine ⟨t, ⟨⟨n + m + k, (hLength.trans hCopy).trans hCompress⟩,
    ht.ready, ht.code, ht.rip, ht.rsp.trans (hsv.trans hsu), ?_, hAgrees⟩⟩
  simpa only [Compress.outputRegion, registerRegion, hdi', hsv, hsu] using ht.output

end Md5.Proofs.Buffered.Finalize.Digest.Finish
