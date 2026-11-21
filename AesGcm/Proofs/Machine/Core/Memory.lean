import AesGcm.Proofs.Machine.Core.Interface
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.Runtime.Root.Memory

namespace AesGcm.Proofs.Machine.GcmContext

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open Standards.NIST.AES AesGcm.Proofs.Machine.Runtime

theorem ContextIn.of_frame {v : Variant} {key : Vector UInt8 v.keyBytes}
    {base : BitVec 64} {before after : Ram} {regions : List MemoryRegion}
    (h : ContextIn v key base before) (hf : RamWriteFrame before after regions)
    (hout : Outside regions base (size v)) : ContextIn v key base after := by
  have hk : Outside regions (base + 32) (16 * (v.Nr + 1)) :=
    outside_subregion hout (by simp only [size]; omega) (by simp only [size]; omega)
  refine ⟨AES16.scheduleIn_of_frame h.1 hf hk, ?_, ?_, ?_, ?_⟩
  · have ho : Outside regions base 8 := by
      simpa using
        outside_subregion (offset := 0) (count := 8) hout
          (by simp only [size]; omega) (by simp only [size]; omega)
    rw [hf.memLoad_eq ho]
    exact h.2.1
  · rw [hf.memLoad_eq (outside_subregion (offset := 8) (count := 8) hout
      (by simp only [size]; omega) (by simp only [size]; omega))]
    exact h.2.2.1
  · rw [hf.memLoad_eq (outside_subregion (offset := 16) (count := 8) hout
      (by simp only [size]; omega) (by simp only [size]; omega))]
    exact h.2.2.2.1
  · rw [hf.memLoad_eq (outside_subregion (offset := 24) (count := 8) hout
      (by simp only [size]; omega) (by simp only [size]; omega))]
    exact h.2.2.2.2

end AesGcm.Proofs.Machine.GcmContext

namespace AesGcm.Proofs.Machine.Core

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem BufferIn.of_frame {before after : Ram} {regions : List MemoryRegion}
    {descriptor source destination : BitVec 64} {bytes : ByteArray}
    (h : BufferIn before descriptor source destination bytes)
    (hf : RamWriteFrame before after regions)
    (hd : Outside regions descriptor 24) (hs : Outside regions source bytes.size) :
    BufferIn after descriptor source destination bytes := by
  rcases h with ⟨hr, hsource, hdestination, hlength, hread, hbytes, hsep⟩
  refine ⟨hr.of_frame hf, ?_, ?_, ?_, hread.of_frame hf,
    hasBytes_of_frame hf hbytes hs.1 (outside_disjoint_span hs), hsep⟩
  · have hload : Outside regions descriptor 8 :=
      ⟨by have := hd.1; omega, fun r hr ↦ by have := hd.2 r hr; omega⟩
    rw [hf.memLoad_eq hload]
    exact hsource
  · rw [hf.memLoad_eq (outside_subregion (offset := 8) (count := 8) hd (by decide) (by decide))]
    exact hdestination
  · rw [hf.memLoad_eq (outside_subregion (offset := 16) (count := 8) hd (by decide) (by decide))]
    exact hlength

theorem InputsIn.of_frame {use256 : Bool}
    {key : Vector UInt8 (AES16.variant use256).keyBytes} {nonce : Vector UInt8 12}
    {aad : ByteArray} {before after : Ram} {regions : List MemoryRegion}
    {context noncePtr aadPtr aadLength : BitVec 64}
    (h : InputsIn use256 key nonce aad before context noncePtr aadPtr aadLength)
    (hf : RamWriteFrame before after regions)
    (hc : Outside regions context (GcmContext.size (AES16.variant use256)))
    (hn : Outside regions noncePtr 12) (ha : Outside regions aadPtr aad.size) :
    InputsIn use256 key nonce aad after context noncePtr aadPtr aadLength := by
  rcases h with ⟨hcontext, hcontextRead, hnonceRead, hnonce, haadRead, haad, hlength⟩
  exact ⟨hcontext.of_frame hf hc, hcontextRead.of_frame hf, hnonceRead.of_frame hf,
    hasBytes_of_frame hf hnonce hn.1 (outside_disjoint_span hn), haadRead.of_frame hf,
    hasBytes_of_frame hf haad ha.1 (outside_disjoint_span ha), hlength⟩


theorem BufferIn.of_frame_disjoint {before after : Ram} {regions : List MemoryRegion}
    {descriptor source destination : BitVec 64} {bytes : ByteArray}
    (h : BufferIn before descriptor source destination bytes)
    (hf : RamWriteFrame before after regions)
    (hd : Outside regions descriptor 24)
    (hs : ∀ region ∈ regions, (span source bytes.size).Disjoint region) :
    BufferIn after descriptor source destination bytes := by
  rcases h with ⟨hr, hsource, hdestination, hlength, hread, hbytes, hsep⟩
  have hb : source.toNat + bytes.size ≤ 2 ^ 64 :=
    Nat.le_trans hread.low (by decide)
  refine ⟨hr.of_frame hf, ?_, ?_, ?_, hread.of_frame hf,
    hasBytes_of_frame hf hbytes hb hs, hsep⟩
  · have ho : Outside regions descriptor 8 := by
      simpa only [BitVec.add_zero] using
        outside_subregion (offset := 0) (count := 8) hd (by decide) (by decide)
    rw [hf.memLoad_eq ho]
    exact hsource
  · rw [hf.memLoad_eq (outside_subregion (offset := 8) (count := 8) hd (by decide) (by decide))]
    exact hdestination
  · rw [hf.memLoad_eq (outside_subregion (offset := 16) (count := 8) hd (by decide) (by decide))]
    exact hlength

theorem InputsIn.of_frame_disjoint {use256 : Bool}
    {key : Vector UInt8 (AES16.variant use256).keyBytes} {nonce : Vector UInt8 12}
    {aad : ByteArray} {before after : Ram} {regions : List MemoryRegion}
    {context noncePtr aadPtr aadLength : BitVec 64}
    (h : InputsIn use256 key nonce aad before context noncePtr aadPtr aadLength)
    (hf : RamWriteFrame before after regions)
    (hc : Outside regions context (GcmContext.size (AES16.variant use256)))
    (hn : Outside regions noncePtr 12)
    (ha : ∀ region ∈ regions, (span aadPtr aad.size).Disjoint region) :
    InputsIn use256 key nonce aad after context noncePtr aadPtr aadLength := by
  rcases h with ⟨hcontext, hcontextRead, hnonceRead, hnonce, haadRead, haad, hlength⟩
  have hb : aadPtr.toNat + aad.size ≤ 2 ^ 64 :=
    Nat.le_trans haadRead.low (by decide)
  exact ⟨hcontext.of_frame hf hc, hcontextRead.of_frame hf, hnonceRead.of_frame hf,
    hasBytes_of_frame hf hnonce hn.1 (outside_disjoint_span hn), haadRead.of_frame hf,
    hasBytes_of_frame hf haad hb ha, hlength⟩

theorem hasBytes_of_memoryBlock {mem : Ram} {ptr : BitVec 64}
    {block : Standards.NIST.AES.Block}
    (hr : Readable mem ptr 16)
    (hb : Fixslice.memoryBlock mem ptr = Fixslice16.fromStandard block) :
    (span ptr 16).HasBytes mem ⟨block.toArray⟩ := by
  refine ⟨by simp [MemoryRegion.HasLength, span, ByteArray.size], ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have he := congrFun hb ⟨i.val, hi⟩
  change (memByte mem (ptr + BitVec.ofNat 64 i.val)).toBitVec = block[i.val].toBitVec at he
  have hp := hr.present i.val hi
  change mem[BitVec.ofNat 64 (ptr.toNat + i.val)]? = some block[i.val]
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  cases hm : mem[ptr + BitVec.ofNat 64 i.val]? with
  | none => simp [hm] at hp
  | some b =>
    simp only [memByte, PhysicalMemory.read, hm, Option.getD_some] at he
    exact congrArg some (UInt8.toBitVec_inj.mp he)

set_option maxRecDepth 2048 in
theorem memoryBlock_nonce96_of_words (original after : Ram) (noncePtr base : BitVec 64)
    (nonce : Vector UInt8 12)
    (hnonce : (span noncePtr 12).HasBytes original ⟨nonce.toArray⟩)
    (words : ∀ k : Fin 3,
      memLoad after (base + BitVec.ofNat 64 (4 * k.val)) 32 =
      memLoad original (noncePtr + BitVec.ofNat 64 (4 * k.val)) 32)
    (w3 : memLoad after (base + 12) 32 = 0x1000000) :
    Fixslice.memoryBlock after base =
      Fixslice16.fromStandard (nonce ++ #v[(0 : UInt8), 0, 0, 1]) := by
  have nonceByte (i : Fin 12) : memByte original (noncePtr + BitVec.ofNat 64 i.val) = nonce[i] := by
    have h := hnonce.2 ⟨i.val, by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt⟩
    change original[BitVec.ofNat 64 (noncePtr.toNat + i.val)]? = some nonce[i] at h
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    simp only [memByte, PhysicalMemory.read, h, Option.getD_some]
  have copied (i : Fin 12) :
      memByte after (base + BitVec.ofNat 64 i.val) =
      nonce[i] := by
    have h := congrArg (fun w : BitVec 32 ↦ storedByte w (i.val % 4))
      (words ⟨i.val / 4, by omega⟩)
    rw [storedByte_memLoad _ _ _ (by omega), storedByte_memLoad _ _ _ (by omega)] at h
    have heq : 4 * (i.val / 4) + i.val % 4 = i.val := by omega
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add, heq] at h
    simpa only [BitVec.add_assoc] using h.trans (nonceByte i)
  have last (i : Fin 4) :
      memByte after
        (base + BitVec.ofNat 64 (12 + i.val)) =
      (#v[0, 0, 0, 1] : Vector UInt8 4)[i] := by
    have h := congrArg (fun w : BitVec 32 ↦ storedByte w i.val) w3
    rw [storedByte_memLoad _ _ _ (by omega)] at h
    have hs : storedByte (0x1000000#32) i.val = (#v[0, 0, 0, 1] : Vector UInt8 4)[i] := by
      rcases i with ⟨i, hi⟩
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · change storedByte (0x1000000#32) 0 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 1 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 2 = (0 : UInt8)
        decide +kernel
      · change storedByte (0x1000000#32) 3 = (1 : UInt8)
        decide +kernel
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] using h.trans hs
  funext i
  apply congrArg UInt8.toBitVec
  change memByte after (base + BitVec.ofNat 64 i.val) =
    (Vector.append nonce (#v[0, 0, 0, 1] : Vector UInt8 4))[i.val]
  by_cases hi : i.val < 12
  · exact (copied ⟨i.val, hi⟩).trans
      (Vector.getElem_append_left (xs := nonce) (ys := (#v[0, 0, 0, 1] : Vector UInt8 4)) hi).symm
  · have h := last ⟨i.val - 12, by omega⟩
    have hidx : 12 + (i.val - 12) = i.val := by omega
    simp only [hidx] at h
    exact h.trans
      (Vector.getElem_append_right (xs := nonce) (ys := (#v[0, 0, 0, 1] : Vector UInt8 4))
        i.isLt (by omega)).symm

end AesGcm.Proofs.Machine.Core
