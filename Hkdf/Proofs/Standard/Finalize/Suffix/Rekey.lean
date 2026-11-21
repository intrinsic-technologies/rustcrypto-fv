import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Pad
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Execution
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Words
import Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Preservation

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.StreamPadding (base)
open Hkdf.Proofs.Common.StreamPadding.Execution

private theorem preserved_bytes {s t : RamState} {p : BitVec 64} {n : Nat} {bytes : ByteArray}
    (same : (Component.mem p n).Agrees s t)
    (old : (MemoryRegion.mk p.toNat n).HasBytes s.external bytes) :
    (MemoryRegion.mk p.toNat n).HasBytes t.external bytes := by
  refine ⟨old.1, fun i => ?_⟩
  have size : bytes.size = n := old.1
  have hi : i.val < n := size ▸ i.isLt
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (same i.val hi).trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using old.2 i)

private theorem outer_pad (block : ByteArray) :
    HMAC.xorPad (HMAC.xorPad block 0x36) 0x6a = HMAC.xorPad block 0x5c := by
  apply ByteArray.ext
  simp only [HMAC.xorPad, Array.map_map, Function.comp_def, UInt8.xor_assoc]
  rfl

private theorem pad_saved {s t : RamState} {p : BitVec 64}
    (effect : AgreesExcept (Common.Pad.components p) s t) : CalleeSavedRegistersUnchanged s t := by
  intro r member
  apply Common.StreamPadding.reg_agrees effect
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Common.Pad.components, Common.StreamPadding.regIndex, X86.Syntax.Reg.fin] <;> decide

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e0c0)
    (digestBytes : (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes s.external digest)
    (keyBytes : (MemoryRegion.mk (stackPtr initial - 336).toNat 64).HasBytes
      s.external (HMAC.keyBlock digest)) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e240 ∧
      (MemoryRegion.mk (stackPtr initial - 192).toNat 32).HasBytes t.external digest ∧
      RekeyedAt t (stackPtr initial - 120) digest := by
  let p := base .hmac initial
  have readable {q : RamState} (current : Suffix.State initial boundary q) (offset len : Nat)
      (bound : offset + len ≤ 416) : MemReadable q (p + BitVec.ofNat 64 offset) len := by
    have sp : stackPtr q = p := current.rsp
    simpa only [sp] using local_readable .hmac pre current.running sp offset len bound
  have bounds : 344 ≤ p.toNat ∧ p.toNat + 408 + 8 < 2^32 := by
    have sp : stackPtr s = p := state.rsp
    simpa only [sp, Common.StreamPadding.Variant.frame] using local_bounds .hmac pre sp
  have key : (MemoryRegion.mk (p + 72).toNat 64).HasBytes s.external (HMAC.keyBlock digest) := by
    have address : p + 72 = stackPtr initial - 336 := local_address .hmac pre 72 (by decide)
    rw [address]
    exact keyBytes
  obtain ⟨a, stateA, ripA, frameA, _, innerA⟩ := pad false pre state rip key
  obtain ⟨b, stateB, ripB, destinationB, sourceB, countB, frameB, setupB⟩ :=
    setup false pre stateA ripA
  have spA : rspOf a = p := stateA.rsp
  have spB : stackPtr b = p := stateB.rsp
  obtain ⟨ivB, lengthB, regsB⟩ := Words.setup_false_words setupB
    (by rw [spA]; exact readable stateB 248 40 (by decide))
  rw [spA] at ivB lengthB
  have keptB := setup_preserves false setupB 72 64 (by decide) (by decide)
  rw [spA] at keptB
  have innerB := preserved_bytes keptB innerA
  obtain ⟨c, stateC, ripC, frameC, abiC, narrowC, hashC⟩ :=
    compress false pre stateB ripB destinationB sourceB countB
      (by rw [spB]; exact innerB)
      (by rw [spB]; exact ivB)
  rw [spB] at narrowC hashC
  have keptC := compress_preserves p 248 narrowC bounds
  have innerC := preserved_bytes (keptC 72 64 (by decide) (by decide) (by decide)) innerB
  obtain ⟨d, stateD, ripD, frameD, paddingD, outerD⟩ := pad true pre stateC ripC innerC
  change (MemoryRegion.mk (p + 72).toNat 64).HasBytes d.external
    (HMAC.xorPad (HMAC.xorPad (HMAC.keyBlock digest) 0x36) 0x6a) at outerD
  rw [outer_pad] at outerD
  obtain ⟨e, stateE, ripE, destinationE, sourceE, countE, frameE, setupE⟩ :=
    setup true pre stateD ripD
  have spD : rspOf d = p := stateD.rsp
  have spE : stackPtr e = p := stateE.rsp
  obtain ⟨ivE, lengthE⟩ := Words.setup_true_words setupE
    (by rw [spD]; exact readable stateE 8 40 (by decide))
    ((regsB.of_saved abiC.1).of_saved (pad_saved paddingD))
  rw [spD] at ivE lengthE
  have keptE (off len : Nat) (bound : off + len ≤ 416) (afterSlot : 48 ≤ off) :
      (Component.mem (p + BitVec.ofNat 64 off) len).Agrees d e := by
    simpa only [spD] using setup_preserves true setupE off len bound (.inr afterSlot)
  have outerE := preserved_bytes (keptE 72 64 (by decide) (by decide)) outerD
  obtain ⟨f, stateF, ripF, frameF, _, narrowF, hashF⟩ :=
    compress true pre stateE ripE destinationE sourceE countE
      (by rw [spE]; exact outerE) (by rw [spE]; exact ivE)
  rw [spE] at narrowF hashF
  have keptF := compress_preserves p 8 narrowF bounds
  have keptD := pad_preserves p paddingD
  have preservedInner (off len : Nat) (bound : off + len ≤ 416) (afterPad : 136 ≤ off) :
      (Component.mem (p + BitVec.ofNat 64 off) len).Agrees c f := by
    intro i hi
    exact ((keptF off len bound (by decide) (.inr (by omega))) i hi).trans
      (((keptE off len bound (by omega)) i hi).trans
        ((keptD off len bound (.inr afterPad)) i hi))
  obtain ⟨t, stateT, ripT, frameT, copied⟩ := copy pre stateF ripF
  have spF : rspOf f = p := stateF.rsp
  have packed := Words.copy_words (key := digest) copied
    (by rw [spF]; exact readable stateT 288 80 (by decide))
    (by rw [spF, compressBlocks_single _ _ (HMAC.xorPad_keyBlock_size _ _)]
        exact Hkdf.Proofs.Common.hashState_of_bytes hashC
          (preservedInner 248 32 (by decide) (by decide)))
    (by rw [spF]
        exact (agrees_loadBytes (preservedInner 280 8 (by decide) (by decide))).trans
          ((agrees_loadBytes (keptC 280 8 (by decide) (by decide) (by decide))).trans lengthB))
    (by rw [spF, compressBlocks_single _ _ (HMAC.xorPad_keyBlock_size _ _)]
        exact hashF)
    (by rw [spF]
        exact (agrees_loadBytes (keptF 40 8 (by decide) (by decide) (by decide))).trans lengthE)
  have frame := memoryWriteFrame_trans
    (memoryWriteFrame_trans
      (memoryWriteFrame_trans
        (memoryWriteFrame_trans
          (memoryWriteFrame_trans
            (memoryWriteFrame_trans frameA frameB) frameC) frameD) frameE) frameF) frameT
  refine ⟨t, stateT, ripT, digest_after pre frame digestBytes, ?_⟩
  have address : p + 288 = stackPtr initial - 120 := local_address .hmac pre 288 (by decide)
  rwa [spF, address] at packed

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey
