import Md5.Proofs.Buffered.FinalizeReset.Padded
import Md5.Proofs.Buffered.FinalizeReset.Prepare
import Md5.Proofs.Buffered.FinalizeReset.Branch

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem pad_short {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s p : RamState} (hp : Pre boundary message s variant) (h : Prepare.Result boundary message s p variant)
    (hshort : message.size % 64 < 56) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padded message t variant ∧
      AgreesExcept (changes s) s t := by
  obtain ⟨t, ht, hready, hcode, hrip, hframe⟩ := padding_branch (variant := variant) h.ready h.code
    hp.boundaryOutside h.rip (by omega : message.size % 64 < 64) h.remaining
  have hsp : stackPtr t = stackPtr p := hframe.read (n := 64) (r := 4) (by simp)
  have hmem : t.external = p.external := hframe.external (by simp [Component.Covers])
  have hlocal : AgreesExcept (changes p) p t := hframe.mono (by simp [changes])
  have hagrees := agrees_trans hp.toStorage h.agrees_reset hlocal
  have hposition : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) :=
    (hframe.read (by simp)).trans h.position
  have hblocks : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) <<< 9 :=
    (hframe.read (by simp)).trans (h.r14.trans hp.bitBlocks)
  obtain ⟨fuel, ha⟩ := h.advances
  refine ⟨fuel + 2, t, ha.trans ht,
    ⟨agrees_storage h.storage hlocal, hready, hcode, ?_, hposition, hblocks, ?_, ?_⟩, hagrees⟩
  · simpa only [ite_eq_left hshort] using hrip
  · simpa only [hsp, h.rsp, hmem, Finalize.paddedBuffer, ite_eq_left hshort] using h.copied
  · have hx := Block.bytes_of_hasBytes h.padded
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Finalize.size_firstBlock] at hx
    intro i hi
    rw [hsp, h.rsp, hmem]
    simpa only [ite_eq_left hshort, context, Prepare.firstBlock] using hx i (by omega)

end Md5.Proofs.Buffered.FinalizeReset
