import K256.Proofs.Ecdh.Decode.Affine.Contract
import K256.Proofs.Ecdh.Decode.Packing.Guards

namespace K256.Proofs.Ecdh.Decode

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

def workSP (fr : Activation) := fr.rsp - 264

def affineActivation (fr : Activation) (a : Values Value Reg.count) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := workSP fr - 8, ret := 0x121177, rsi := workSP fr + 72,
    rdi := workSP fr + 144, rbp := a[5].get 64, rbx := a[3].get 64, r12 := a[12].get 64,
    r13 := a[13].get 64, r14 := a[14].get 64, r15 := a[15].get 64,
    mxcsr := a[39].get 32, ftw := a[50].get 16, fcw := a[51].get 16 }

theorem workSP_offset {fr : Activation} (room : fr.low.toNat + 1464 ≤ fr.rsp.toNat)
    (off : BitVec 64) (h : (264 - off).toNat ≤ 1464) :
    (workSP fr + off).toNat = fr.rsp.toNat - (264 - off).toNat := by
  rw [show workSP fr + off = fr.rsp - (264 - off) by unfold workSP; bv_omega,
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]

theorem stackWindow {fr : Activation} (wr : Writable Extracted.programImage fr.original (fr.rsp-1464) 1464) :
    Writable Extracted.programImage fr.original (workSP fr-8) 272 := by
  exact wr.of_offsets (x := fr.rsp) (c := 0-272) (by unfold workSP; bv_omega) (addr_sub _ _) (by decide)

private theorem packedImageLoaded {fr : Activation} {m : Ram}
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    (wr : Writable Extracted.programImage fr.original (workSP fr-8) 272)
    (frame : RamWriteFrame fr.original m [Packing.window (workSP fr)]) :
    ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2 := by
  intro x hx
  let base := workSP fr-8
  apply (frame.outside x.1 ?_).trans (image x hx)
  refine ⟨by have := x.1.isLt; omega, ?_⟩
  rintro r hr
  obtain rfl := List.mem_singleton.mp hr
  change x.1.toNat + 1 ≤ base.toNat ∨ base.toNat + 272 ≤ x.1.toNat
  apply Classical.byContradiction
  intro bad
  have idx : x.1.toNat-base.toNat < 272 := by omega
  apply wr.notCode x hx _ idx
  apply BitVec.eq_of_toNat_eq
  symm
  change (base + BitVec.ofNat 64 (x.1.toNat - base.toNat)).toNat = x.1.toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _-_) (by omega),
    Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt x.1.isLt]

theorem affineEntry {fr : Activation} {a : Values Value Reg.count} {m : Ram} {bytes : ByteArray}
    (room : fr.low.toNat + 1464 ≤ fr.rsp.toNat) (align : fr.rsp.toNat % 16 = 8)
    (wr : Writable Extracted.programImage fr.original (fr.rsp-1464) 1464)
    (text : fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat-1464)
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    (frame : RamWriteFrame fr.original m [Packing.window (workSP fr)])
    (rsp : a[4] = ⟨64,workSP fr-8⟩) (src : a[6] = ⟨64,workSP fr+72⟩)
    (dst : a[7] = ⟨64,workSP fr+144⟩) (r8 : a[8].width = 64) (r9 : a[9].width = 64)
    (df : a[22] = ⟨1,0⟩)
    (saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,39,50,51] →
      a[i] = (affineActivation fr a m).entryValue i.val)
    (ret : memLoad m (workSP fr-8) 64 = 0x121177)
    (bytesAt : ∀ i < 65, memByte m (workSP fr+72 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) :
    Affine.Entry (affineActivation fr a m) a m bytes := by
  have w := wr.of_frame frame
  have nat : (workSP fr-8).toNat = fr.rsp.toNat-272 := by
    rw [show workSP fr-8 = fr.rsp-272 by unfold workSP; bv_omega,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 272 ≤ fr.rsp.toNat; omega))]
    rfl
  have ns : (workSP fr+72).toNat = fr.rsp.toNat-192 := workSP_offset room 72 (by decide)
  have nd : (workSP fr+144).toNat = fr.rsp.toNat-120 := workSP_offset room 144 (by decide)
  refine ⟨rsp,src,dst,r8,r9,df,saved,?_,?_,?_,?_,ret,by change (0x121177 : BitVec 64).toNat < 2^32; decide,?_,bytesAt,?_,?_,?_,
    packedImageLoaded image (stackWindow wr) frame,?_⟩
  · change Writable _ m (workSP fr-8-1192) 1192
    apply w.of_offsets (x := fr.rsp) (c := 0-1464) (by unfold workSP; bv_omega) (addr_sub _ _) (by decide)
  · change fr.low.toNat + 1192 ≤ (workSP fr-8).toNat; omega
  · change (workSP fr-8).toNat % 16 = 8; omega
  · change Readable m (workSP fr-8) 8
    exact (stackWindow wr).readable.of_frame frame |>.sub (Nat.le_refl _) (by omega)
  · exact w.readable.of_offsets (x := fr.rsp) (c := 0-192) (by change workSP fr+72 = _; unfold workSP; bv_omega)
      (addr_sub _ _) (by decide)
  · exact w.of_offsets (x := fr.rsp) (c := 0-120) (by change workSP fr+144 = _; unfold workSP; bv_omega)
      (addr_sub _ _) (by decide)
  · change (workSP fr-8).toNat + 8 ≤ (workSP fr+72).toNat; omega
  · change (workSP fr-8).toNat + 8 ≤ (workSP fr+144).toNat; omega
  · change (workSP fr-8).toNat-136 ≤ _ ∨ _ ≤ (workSP fr-8).toNat-1192; omega

end K256.Proofs.Ecdh.Decode
