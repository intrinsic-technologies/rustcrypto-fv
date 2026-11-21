import Md5.Proofs.Buffered.FinalizeReset.Compression
import Md5.Proofs.Buffered.FinalizeReset.Export
import Md5.Proofs.Buffered.FinalizeReset.Padded
import Md5.Proofs.Buffered.FinalizeReset.Copy.Result
import Md5.Proofs.Buffered.FinalizeReset.CopyBridge
import Md5.Proofs.Buffered.FinalizeReset.Length.Properties

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure FinalBlock [Bindings] (message : ByteArray) (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = (variant.address 0x100917)
  rdi : s.regValue .rdi = stackPtr s + 0xe8
  rsi : s.regValue .rsi = stackPtr s + 0x60
  rdx : s.regValue .rdx = 1
  input : (⟨(stackPtr s + 0x60).toNat, 64⟩ : MemoryRegion).HasBytes
    s.external (Finalize.lastBlock message)
  buffer : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(Finalize.paddedBuffer message).toBytes.toArray⟩

theorem finalBlock_of_copy {variant : Variant} [Bindings] {message : ByteArray} {s u v : RamState}
    (h : Padded message s variant) (hl : (Length.effect s variant).Holds s u)
    (hc : Copy.Result .finalBlock u v variant) : FinalBlock message v variant := by
  have hal := Length.effect_agrees hl
  have hsu := agrees_storage h.toStorage hal
  have hasp := agrees_rsp hal
  have hac := Copy.agrees_reset hc.agrees
  have hsv := agrees_storage hsu hac
  have hb : (⟨(stackPtr u + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes u.external
      ⟨(Finalize.paddedBuffer message).toBytes.toArray⟩ := by
    rw [hasp]
    exact Length.effect_buffer hl h.buffer
  have hd := Length.effect_lastBlock h.toStorage hl h.position h.bitBlocks h.prefixBytes
  have hi : (⟨(stackPtr u + 8).toNat, 64⟩ : MemoryRegion).HasBytes
      u.external (Finalize.lastBlock message) := by simpa only [hasp] using hd.1
  have hlen : Bytes u.external (stackPtr u + 152) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by simpa only [hasp] using hd.2
  refine ⟨hsv, hc.ready, hc.code, hc.rip, ?_, ?_, hc.rdx, ?_, ?_⟩
  · change (Operand.reg 7 : Operand 64).read v = _
    rw [hc.rsp]
    exact hc.rdi
  · change (Operand.reg 6 : Operand 64).read v = _
    rw [hc.rsp]
    exact hc.rsi
  · rw [hc.rsp]
    exact Copy.lastBlock_hasBytes hc.agrees hc.copied hi hlen
  · rw [hc.rsp]
    exact Copy.preserves_buffer hc.agrees hb

theorem compress_export {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : FinalBlock message s variant) (hout : ¬ InProgram boundary.rip) :
    ∃ t, Post boundary message s t variant := by
  obtain ⟨u, hc⟩ := Compression.last (variant := variant)
    (Compression.pre h.toStorage (Finalize.size_lastBlock message) h.rdi h.rsi h.rdx h.input h.buffer)
    h.ready h.code hout h.rip
  have hframe := Compression.agrees h.rdi hc.agrees
  have hstorage := agrees_storage h.toStorage hframe
  have hdigest : (⟨(stackPtr u + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes u.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message)).toArray⟩ := by
    rw [Finalize.messageDigest_paddedBuffer, hc.rsp]
    simpa only [Compress.outputRegion, registerRegion, h.rdi] using hc.output
  obtain ⟨t, he⟩ := export_digest (variant := variant)
    (boundary := boundary) ⟨⟨hstorage, hc.rip⟩, hc.ready, hc.code, hout, hdigest⟩
  obtain ⟨fuel, hr⟩ := hc.advances
  have hpost : Post boundary message u t variant :=
    ⟨he.advances, he.ready, he.code, he.rip, he.absorbed, he.digest, he.agrees⟩
  exact ⟨t, hpost.prepend h.toStorage hr hframe⟩

end Md5.Proofs.Buffered.FinalizeReset
