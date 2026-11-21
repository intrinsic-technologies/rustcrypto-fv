import K256.Proofs.Verify.Transfer.PublicKey.Affine.Decoder
import K256.Proofs.Ecdh.Decode.Affine.Coordinates

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Affine Standards.SECG.ECC K256.Proofs.Ecdh.Decode.Affine

def uncompressedFrame (fr : Activation) (n : Ram) : Activation :=
  {fr with
    original := n, rsp := fr.rsp-136-8, low := fr.rsp-136-8-1048, ret := 0x121502,
    rdi := fr.rsp-136, rsi := fr.rsi+1, rbx := fr.rdi, r14 := fr.rsi+1, rdx := fr.rsi+33}

private theorem coordinateValue {fr args m bytes n} (e : Entry fr args m bytes)
    (frame : RamWriteFrame m n [⟨(fr.rsp-145).toNat,145⟩]) (size : bytes.size = 65)
    (off : Nat) (fit : off+32 ≤ bytes.size) :
    Encoding.octetsToNat (bytes.extract off (off+32)) =
      (Uncompressed.readCoordinate n (fr.rsi + BitVec.ofNat 64 off)).nat := by
  have padded := e.input.of_frame frame
  have sourceLow := padded.low
  have room := e.low
  have above := e.srcAbove
  have packed : (⟨fr.rsi.toNat, bytes.size⟩ : MemoryRegion).HasBytes n bytes := by
    refine ⟨rfl, fun i => ?_⟩
    have hi : i.val < 65 := by have := i.isLt; omega
    let addr := fr.rsi + BitVec.ofNat 64 i.val
    have addrNat : addr.toNat = fr.rsi.toNat + i.val := by
      dsimp only [addr]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := i.val) (by omega), Nat.mod_eq_of_lt (by omega)]
    have preserved : Outside [⟨(fr.rsp - 145).toNat, 145⟩] addr 1 := by
      refine ⟨by rw [addrNat]; omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change (fr.rsp - 145).toNat + 145 ≤ addr.toNat
      rw [addrNat, BitVec.toNat_sub_of_le (by change 145 ≤ fr.rsp.toNat; omega)]
      change fr.rsp.toNat - 145 + 145 ≤ fr.rsi.toNat + i.val
      omega
    have content := e.bytesAt i.val hi
    change memByte m addr = bytes.data[i.val]?.getD 0 at content
    have present : (n[addr]?).isSome := padded.present i.val hi
    change n[BitVec.ofNat 64 (fr.rsi.toNat + i.val)]? = some bytes[i.val]
    rw [K256.Proofs.ofNat_toNat_add]
    change n[addr]? = _
    change (m[addr]?).getD 0 = _ at content
    rw [← frame.outside addr preserved] at content
    have hi' : i.val < bytes.data.size := i.isLt
    rw [Array.getElem?_eq_getElem hi', Option.getD_some,
      ← ByteArray.getElem_eq_getElem_data] at content
    rw [← content]
    exact (Option.getD_of_ne_none (Option.ne_none_iff_isSome.mpr present) 0).symm
  have h := Common.octetsToNat_extract_eq_words (off := off) packed fit
  unfold Uncompressed.CoordinateWords.nat Uncompressed.CoordinateWords.limbs Uncompressed.readCoordinate
  rw [Uncompressed.unpack_value]
  simpa only [K256.Proofs.ofNat_toNat_add,Common.scalarWord,Nat.reduceSub,Nat.reduceMul,
    BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h

set_option maxRecDepth 4096 in
theorem uncompressedChild {fr args m bytes child n} {p : Curve.Point} (e : Entry fr args m bytes)
    (regs : CoordinateRegisters (uncompressedFrame fr n) child)
    (ret : memLoad n (fr.rsp-136-8) 64 = 0x121502)
    (frame : RamWriteFrame m n [⟨(fr.rsp-145).toNat,145⟩])
    (size : bytes.size = 65) (header : bytes.data[0]? = some 4)
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some p) :
   ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11f780,child,n⟩,[]⟩ out ∧
     out.tag = some ⟨64,0x121502⟩ ∧ out.values[4] = ⟨64,fr.rsp-136⟩ ∧
     (∀ i : Fin Reg.count, i.val ∈ [3,13,22,39,50,51] → out.values[i] = child[i]) ∧
     RamWriteFrame n out.store (coordinateWrites fr) ∧ memLoad out.store (fr.rsp-136+88) 8 = 1 ∧
     Ecdh.Decode.AffinePointAt out.store (fr.rsp-136) p := by
  let cf := uncompressedFrame fr n
  have room := e.low
  have above := e.srcAbove
  have srcLow := e.input.low
  have spNat : cf.rsp.toNat = fr.rsp.toNat-144 := by
    change (fr.rsp-136-8).toNat = _
    rw [BitVec.sub_sub]
    exact BitVec.toNat_sub_of_le (by change 144 ≤ fr.rsp.toNat; omega)
  have dstNat : cf.rdi.toNat = fr.rsp.toNat-136 :=
    BitVec.toNat_sub_of_le (by change 136 ≤ fr.rsp.toNat; omega)
  have lowEq : cf.low = fr.rsp-1192 := by
    change fr.rsp-136-8-1048 = fr.rsp-1192
    bv_omega
  have bottom : (fr.rsp-1192).toNat = fr.rsp.toNat-1192 :=
    BitVec.toNat_sub_of_le (by change 1192 ≤ fr.rsp.toNat; omega)
  have lowNat : cf.low.toNat = fr.rsp.toNat-1192 := (congrArg BitVec.toNat lowEq).trans bottom
  have srcNat : cf.rsi.toNat = fr.rsi.toNat+1 := by
    change (fr.rsi+1).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsi.toNat+1 < 2^64; omega)]
    rfl
  have win := e.window.of_frame frame
  have stack : Writable Extracted.programImage n (cf.rsp-1048) 1048 := by
    change Writable _ _ cf.low _
    rw [lowEq]
    exact win.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _)
  have slot : Readable n cf.rsp 8 := win.readable.sub (by omega) (by omega)
  have dst : Writable Extracted.programImage n cf.rdi 89 := win.sub (by omega) (by omega)
  have src : Readable n cf.rsi 32 := (e.input.of_frame frame).sub (by omega) (by omega)
  have yn : cf.rdx.toNat = fr.rsi.toNat+33 := by
    change (fr.rsi+33).toNat = _
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by change fr.rsi.toNat+33 < 2^64; omega)]
    rfl
  have srcY : Readable n cf.rdx 32 := (e.input.of_frame frame).sub (by omega) (by omega)
  have width (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : child[i] = ⟨64,child[i].get 64⟩ := by
    have h := regs.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;omega)
    rw [h]
    rcases i with ⟨i,hi'⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have pre : Uncompressed.EntryPre Extracted.programImage child n cf.rsp cf.rdi cf.rsi cf.rdx cf.ret :=
    ⟨congrArg (Value.get 64) regs.rsp,congrArg (Value.get 64) regs.rdi,congrArg (Value.get 64) regs.rsi,
      congrArg (Value.get 64) regs.rdx,width,stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide),
      by omega,slot,ret,by change (0x121502 : BitVec 64).toNat < 2^32; decide,dst,src,srcY,.inr (by omega),.inr (by omega),.inr (by omega)⟩
  obtain ⟨out,run,tag,sp,_,keep,writes,flag,point⟩ :=
    affineDecoder Common.fnCode_subset_programImage child n _ _ _ _ _ pre
  have childWrites := (RamWriteFrame.refl n (coordinateWrites fr)).trans writes (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have a : (cf.rsp-273).toNat = cf.rsp.toNat-273 := BitVec.toNat_sub_of_le (by change 273 ≤ cf.rsp.toNat; omega)
      refine ⟨_,List.mem_cons_self,?_,?_⟩
      · change cf.low.toNat ≤ (cf.rsp-273).toNat; omega
      · change (cf.rsp-273).toNat + 273 ≤ cf.low.toNat + 1048; omega
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  refine ⟨out,run,tag,sp.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel (fr.rsp-136) (8 : BitVec 64))),
    fun i hi => keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;omega),childWrites,?_⟩
  have x := coordinateValue e frame size 1 (by omega)
  have y := coordinateValue e frame size 33 (by omega)
  have spec := Sec1.decodePublicKey_uncompressed size header
  rw [x,y,decoded] at spec
  dsimp only at spec
  split at spec
  · rename_i ok
    cases Option.some.inj spec
    exact ⟨flag.trans (congrArg (fun b : Bool => BitVec.ofNat 8 b.toNat) ok),point ok⟩
  · cases spec

end K256.Proofs.Verify.Transfer.PublicKey
