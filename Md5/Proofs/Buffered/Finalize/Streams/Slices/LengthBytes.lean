import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length.Properties
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.LengthBytes

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Blocks.Length

theorem prefix_bytes {update : Bool} [Bindings] {message : ByteArray} {s t : RamState}
    (h : LengthReady (update := update) message s) (he : (effect (update := update) s).Holds s t) :
    Bytes t.external (stackPtr t + 16) 56
      (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0) := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    rw [effect_rsp he]
    intro i hi
    exact (effect_byte he (offset := 16) (by unfold OffsetsApart; decide)
      (by unfold OffsetsApart; decide) (by decide) hi).trans
      (h.prefixBytes i hi)

theorem buffer_bytes {update : Bool} [Bindings] {message : ByteArray} {s t : RamState}
    (h : LengthReady (update := update) message s) (he : (effect (update := update) s).Holds s t) :
    (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(paddedBuffer message).toBytes.toArray⟩ := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    rw [effect_rsp he]
    refine ⟨h.buffer.1, ?_⟩
    intro i
    have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hb := h.buffer.2 i
    change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + i.val)]? = _
    change s.external[BitVec.ofNat 64 ((stackPtr s).toNat + i.val)]? = _ at hb
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
    have heq := effect_byte he (offset := 0) (len := 16)
      (by unfold OffsetsApart; decide) (by unfold OffsetsApart; decide) (by decide) hi
    simpa using heq.trans (by simpa using hb)

theorem length_bytes {update : Bool} [Bindings] {message : ByteArray} {s t : RamState}
    (h : LengthReady (update := update) message s) (he : (effect (update := update) s).Holds s t) :
    Bytes t.external (stackPtr t + 160) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    rw [effect_rsp he]
    apply Stores.bytes_of_read_eq
      (Stores.readable_of_agrees (h.toStorage.stackWritable 160 8 (by decide)).readable he.agrees)
    exact he.writes.2.2.2.trans (value_eq h.position h.blocks)

end Md5.Proofs.Buffered.Finalize.Streams.Slices.LengthBytes
