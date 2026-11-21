import K256.Proofs.Ecdh.Decode.Affine.Contract
import K256.Proofs.Verify.Transfer.PublicKey.Packing.Guards
import K256.Proofs.Verify.Transfer.PublicKey.Packing.Widths
import K256.Proofs.Sec1.Parser.Frame.Entry
import K256.Proofs.Sec1.LIR.Fn106390.Frame
import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.ParseSignature.Contract
import K256.Spec.Secp256k1

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR Standards.SECG.ECC

def affineFrame (fr : Activation) (m : Ram) : Activation :=
  {fr with original := m, rsp := fr.rsp-344-8, rsi := fr.rsp-344+4, rdi := fr.rsp-344+160,
           ret := 0x1064f4, rbx := fr.rsp-344+160, r12 := 0, r14 := fr.rdx, r15 := fr.rdi}

def saved (fr : Activation) (m : Ram) : Prop :=
  memLoad m (fr.rsp-32) 64 = fr.rbx ∧ memLoad m (fr.rsp-24) 64 = fr.r12 ∧
  memLoad m (fr.rsp-16) 64 = fr.r14 ∧ memLoad m (fr.rsp-8) 64 = fr.r15 ∧ memLoad m fr.rsp 64 = fr.ret

private theorem loadedAfterWrites {base : BitVec 64} {k : Nat} {m n : Ram}
    (w : Writable Extracted.programImage m base k)
    (f : RamWriteFrame m n [ParseSignature.buffer base k])
    (loaded : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2) :
    ∀ x ∈ Extracted.programImage, n[x.1]? = some x.2 := by
  intro x hx
  apply (f.outside x.1 ?_).trans (loaded x hx)
  refine ⟨by have := x.1.isLt; omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change x.1.toNat + 1 ≤ base.toNat ∨ base.toNat + k ≤ x.1.toNat
  apply Classical.byContradiction
  intro bad
  apply w.notCode x hx (x.1.toNat-base.toNat) (by omega)
  rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]

open Sec1.Parser Sec1.Parser.Packing

theorem pack (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn106390.frameAt .l106390 fr))
    (len : fr.rdx = 65) (src : Readable fr.original fr.rsi 65)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 65)
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    (text : fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat - 1544)
    {bytes : ByteArray} (size : bytes.size = 65) (head : bytes.data[0]? = some 4)
    (bytesAt : (⟨fr.rsi.toNat,65⟩ : MemoryRegion).HasBytes fr.original bytes) :
    ∃ b m, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l106390,a,fr.original⟩,[]⟩ ⟨⟨.l121480,b,m⟩,[Sec1.Parser.Packing.affineResume]⟩ ∧
      Ecdh.Decode.Affine.Entry (affineFrame fr m) b m bytes ∧ saved fr m ∧
      RamWriteFrame fr.original m [fr.region] := by
  simp only [Fn106390.frameAt, Fn106390.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp, df, _, dx, bx, bp, si, di, _, r9, r12, r13, r14, r15, mx, ft, fc,
    slot, ret, _, stack, room, align, _, _, _, _, _, _, _, _, gotBound, _⟩ := entry
  let sp := fr.rsp - 344
  let mem := Frame.savedRegistersMemory fr.original fr.rsp a
  let region := ParseSignature.buffer (fr.rsp - 1544) 1544
  change fr.low.toNat + 1544 ≤ fr.rsp.toNat at room
  have sub (d : BitVec 64) (hd : d.toNat ≤ 1544) : (fr.rsp - d).toNat = fr.rsp.toNat - d.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have start : region.start = fr.rsp.toNat - 1544 := sub 1544 (by decide)
  have stop : region.start + region.size = fr.rsp.toNat := by rw [start]; change _ + 1544 = _; omega
  have nsp : sp.toNat = fr.rsp.toNat - 344 := sub 344 (by decide)
  have nslot : (sp-8).toNat = fr.rsp.toNat-352 := by
    rw [show sp-8 = fr.rsp-352 by dsimp [sp]; bv_omega]; exact sub 352 (by decide)
  have n32 := sub 32 (by decide)
  change (fr.rsp-32).toNat = fr.rsp.toNat-32 at n32
  have low := slot.low
  have wr : Writable Extracted.programImage fr.original (fr.rsp-32) 32 :=
    stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have firstFrame : RamWriteFrame fr.original mem [region] :=
    Frame.savedRegistersMemory_frame a wr ⟨_,.head _, by omega, by omega, by omega⟩
  have loaded := loadedAfterWrites stack firstFrame image
  have outsideSrc := srcApart.2 _ (List.mem_singleton_self _)
  change fr.rsi.toNat + 65 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat at outsideSrc
  have srcLow := src.low
  have input (i : Nat) (hi : i < bytes.size) :
      memByte mem (fr.rsi + BitVec.ofNat 64 i) = bytes[i] := by
    have loc : (fr.rsi + BitVec.ofNat 64 i).toNat = fr.rsi.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
    have outside : Outside [region] (fr.rsi + BitVec.ofNat 64 i) 1 := by
      refine ⟨by omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      omega
    have h := bytesAt.2 ⟨i, hi⟩
    simp only [ofNat_toNat_add] at h
    exact congrArg (fun v : Option UInt8 => v.getD 0) ((firstFrame.outside _ outside).trans h)
  have srcRead := src.of_frame firstFrame
  have read : LoadOk mem fr.rsi 1 := ⟨by omega, fun i hi => srcRead.present i (by omega)⟩
  have pos : 0 < bytes.size := by omega
  have first : bytes[0]'pos = 4 := by
    rw [Array.getElem?_eq_getElem (by exact pos)] at head
    exact Option.some.inj head
  have tag : memLoad mem fr.rsi 8 = 4 := by
    apply memLoad_eq_of_memByte (by decide)
    intro i hi
    obtain rfl : i = 0 := by omega
    exact (input 0 pos).trans first
  obtain ⟨after, step, moved, keeps⟩ := Frame.entryBlock (congrArg (Value.get 64) rsp)
    ((congrArg (Value.get 64) dx).trans len) wr (fun x hx => Common.fnCode_subset_programImage x (code_l106390 x hx))
  rw [ite_eq_right (by decide)] at step
  obtain ⟨ready, guards, kept, wr8, wr9⟩ := uncompressedGuards
    (congrArg (Value.get 64) ((keeps 6 (by decide)).trans si))
    ((congrArg (Value.get 64) ((keeps 2 (by decide)).trans dx)).trans len)
    (congrArg Value.width ((keeps 9 (by decide)).trans r9)) read tag loaded
  have unchanged (i : Fin Reg.count) (h : i.val ∈ [2,5,6,7,12,13,22,39,50,51]) : ready[i] = a[i] := by
    apply (kept i ?_).trans (keeps i ?_) <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;> omega
  have win : Writable Extracted.programImage mem (sp-8) 233 :=
    (stack.of_offsets (x := fr.rsp) (c := 0-352) (by dsimp [sp]; bv_omega) (addr_sub _ _) (by decide)).of_frame firstFrame
  have sep : Outside [packingWindow sp] fr.rsi bytes.size := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (sp-8).toNat ∨ (sp-8).toNat+233 ≤ _
    omega
  have apart : Outside [packingWindow sp] 0x203dd0 8 := by
    refine ⟨by decide, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change 0x203dd8 ≤ (sp-8).toNat ∨ (sp-8).toNat+233 ≤ 0x203dd0
    omega
  have slots := Fn106390.callSlots_loaded (sections := Extracted.programSections)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) loaded
  obtain ⟨sr, sv⟩ := slots (0x203e10, 0x12a700) (by decide)
  obtain ⟨cr, cv⟩ := slots (0x203dd0, 0x12a820) (by decide)
  obtain ⟨b, m, run, w8, w9, obx, osp, osi, odi, o12, o14, o15, encoded, retWord, f, keep⟩ :=
    acceptedEncodingWidths (bytes := bytes) [] (sp := sp) wr8 wr9
      (congrArg (Value.get 64) ((kept 4 (by decide)).trans moved))
      (congrArg (Value.get 64) ((unchanged 6 (by decide)).trans si))
      (congrArg (Value.get 64) ((unchanged 7 (by decide)).trans di))
      (congrArg (Value.get 64) ((unchanged 2 (by decide)).trans dx))
      (congrArg (Value.get 1) ((unchanged 22 (by decide)).trans df))
      (by rw [len, size]; rfl) (.inr (.inr len)) (by omega) win (size ▸ srcRead) sep input
      Common.fnCode_subset_programImage ⟨sr.low, sr.present⟩ sv cr cv apart
  have total : RamWriteFrame fr.original m [region] := by
    apply firstFrame.trans f
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨region, .head _, by change _ ≤ (sp-8).toNat; omega, by change (sp-8).toNat+233 ≤ _; omega⟩
  have preserved (i : Fin Reg.count) (h : i.val ∈ [5,13,22,39,50,51]) : b[i] = a[i] :=
    (keep i h i.isLt).trans (unchanged i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢; omega))
  refine ⟨b,m, ((reaches_jump step).trans guards).trans run, ?_, ?_, ?_⟩
  · have finalStack := stack.of_frame total
    have offset (k : BitVec 64) (hk : k.toNat ≤ 344) :
        (sp+k).toNat = fr.rsp.toNat-(344-k.toNat) := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    have nsi := offset 4 (by decide)
    have ndi := offset 160 (by decide)
    refine ⟨osp,osi,odi,w8,w9,(preserved 22 (by decide)).trans df,?_,?_,?_,?_,?_,retWord,
      by change (0x1064f4 : BitVec 64).toNat < 2^32; decide,?_,encoded,?_,?_,?_,loadedAfterWrites stack total image,?_⟩
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact obx | exact o12 | exact o14 | exact o15
        | exact (preserved 5 (by decide)).trans bp | exact (preserved 13 (by decide)).trans r13
        | exact (preserved 39 (by decide)).trans mx | exact (preserved 50 (by decide)).trans ft
        | exact (preserved 51 (by decide)).trans fc
    · exact finalStack.of_offsets (x := fr.rsp) (c := 0-1544) (by change sp-8-1192 = _; dsimp [sp]; bv_omega) (addr_sub _ _) (by decide)
    · change fr.low.toNat+1192 ≤ (sp-8).toNat; omega
    · change (sp-8).toNat % 16 = 8; omega
    · change Readable m (sp-8) 8
      exact (win.readable.of_frame f).sub (Nat.le_refl _) (by omega)
    · exact finalStack.readable.of_offsets (x := fr.rsp) (c := 0-340) (by change sp+4 = _; dsimp [sp]; bv_omega) (addr_sub _ _) (by decide)
    · exact finalStack.of_offsets (x := fr.rsp) (c := 0-184) (by change sp+160 = _; dsimp [sp]; bv_omega) (addr_sub _ _) (by decide)
    · change (sp-8).toNat+8 ≤ (sp+4).toNat; omega
    · change (sp-8).toNat+8 ≤ (sp+160).toNat; omega
    · change (sp-8).toNat-136 ≤ _ ∨ _ ≤ (sp-8).toNat-1192; omega
  · obtain ⟨s3,s12,s14,s15,sret⟩ := Frame.savedRegistersMemory_load fr.original fr.rsp a
    have same (p : BitVec 64) (ha : fr.rsp.toNat-32 ≤ p.toNat) (hb : p.toNat ≤ fr.rsp.toNat) :
        memLoad m p 64 = memLoad mem p 64 := by
      apply f.memLoad_eq
      refine ⟨by change p.toNat+8 ≤ 2^64; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inr (by change (sp-8).toNat+233 ≤ _; omega)
    have s (k : BitVec 64) (hk : k.toNat ≤ 32) := same (fr.rsp-k)
      (by rw [sub k (by omega)]; omega) (by rw [sub k (by omega)]; omega)
    exact ⟨(s 32 (by decide)).trans (s3.trans (congrArg (Value.get 64) bx)),
      (s 24 (by decide)).trans (s12.trans (congrArg (Value.get 64) r12)),
      (s 16 (by decide)).trans (s14.trans (congrArg (Value.get 64) r14)),
      (s 8 (by decide)).trans (s15.trans (congrArg (Value.get 64) r15)),
      (same _ (by omega) (Nat.le_refl _)).trans (sret.trans ret)⟩
  · apply (RamWriteFrame.refl _ _).trans total
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨fr.region, .head _, by change fr.low.toNat ≤ _; omega,
      by change _ ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega⟩

end K256.Proofs.Verify.Transfer.PublicKey
