import K256.Proofs.Ecdh.Decode.Affine.Contract
import K256.Proofs.Ecdh.Decode.Compressed

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Affine Standards.SECG.ECC

def childFrame (fr : Activation) (m : Ram) (tag : BitVec 8) : Activation :=
  {fr with original := m, rsp := fr.rsp-136-8, low := fr.rsp-1192, ret := 0x1214ce,
           rdi := fr.rsp-136, rsi := fr.rsi+1, rbx := fr.rdi, r14 := fr.rsi+1, rdx := if tag = 3 then 1 else 0}

private theorem Entry.coordinates {fr args m bytes n} (e : Entry fr args m bytes)
    (frame : RamWriteFrame m n [⟨(fr.rsp-145).toNat,145⟩]) (size : bytes.size = 33) :
    Encoding.octetsToNat (bytes.extract 1 33) = (Compressed.inputs n (fr.rsi+1)).x := by
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
  have h := Common.octetsToNat_extract_eq_words (off := 1) packed (by omega)
  dsimp only [Compressed.Inputs.x, Compressed.inputs, Uncompressed.CoordinateWords.nat,
    Uncompressed.CoordinateWords.limbs, Uncompressed.readCoordinate]
  rw [Uncompressed.unpack_value]
  simpa only [K256.Proofs.ofNat_toNat_add,Common.scalarWord,Nat.reduceSub,Nat.reduceMul,
    BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.reduceAdd] using h

private theorem preservedAfterReturn {fr : Activation} {args : Values Value Reg.count}
    {out : Output Value Ram Reg.count} (regs : CoordinateRegisters fr args)
    (done_ : Atom.All Extracted.programImage out.values out.store (Fn1205b0.doneAt fr)) :
    ∀ i : Fin Reg.count, i.val ∈ [3,13,22,39,50,51] → out.values[i] = args[i] := by
  simp only [Fn1205b0.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨_,df,bx,_,_,r13,_,_,mx,ft,fc,_⟩ := done_
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bx.trans (regs.saved 3 (by decide)).symm
  · exact r13.trans (regs.saved 13 (by decide)).symm
  · exact df.trans regs.df.symm
  · exact mx.trans (regs.saved 39 (by decide)).symm
  · exact ft.trans (regs.saved 50 (by decide)).symm
  · exact fc.trans (regs.saved 51 (by decide)).symm

set_option maxRecDepth 4096 in
theorem childExecution {fr args m bytes child n} {tag : UInt8} {p : Curve.Point} (e : Entry fr args m bytes)
    (regs : CoordinateRegisters (childFrame fr n tag.toBitVec) child)
    (ret : memLoad n (fr.rsp-136-8) 64 = 0x1214ce)
    (frame : RamWriteFrame m n [⟨(fr.rsp-145).toNat,145⟩])
    (valid : tag = 2 ∨ tag = 3 ∨ tag = 5) (size : bytes.size = 33)
    (decoded : Sec1.decompress (if tag = 5 then 2 else tag) (Encoding.octetsToNat (bytes.extract 1 33)) = some p) :
   ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1205b0,child,n⟩,[]⟩ out ∧
     out.tag = some ⟨64,0x1214ce⟩ ∧ out.values[4] = ⟨64,fr.rsp-136⟩ ∧
     (∀ i : Fin Reg.count, i.val ∈ [3,13,22,39,50,51] → out.values[i] = child[i]) ∧
     RamWriteFrame n out.store (coordinateWrites fr) ∧ memLoad out.store (fr.rsp-136+88) 8 = 1 ∧
     AffinePointAt out.store (fr.rsp-136) p := by
  let cf := childFrame fr n tag.toBitVec
  let want := cf.rdx.setWidth 8
  let t := if tag = 5 then (2 : UInt8) else tag
  have room := e.low
  have align := e.align
  have above := e.srcAbove
  have srcLow := e.input.low
  have spNat : cf.rsp.toNat = fr.rsp.toNat-144 := by
    change (fr.rsp-136-8).toNat = _
    rw [BitVec.sub_sub]
    exact BitVec.toNat_sub_of_le (by change 144 ≤ fr.rsp.toNat; omega)
  have dstNat : cf.rdi.toNat = fr.rsp.toNat-136 :=
    BitVec.toNat_sub_of_le (by change 136 ≤ fr.rsp.toNat; omega)
  have lowNat : cf.low.toNat = fr.rsp.toNat-1192 :=
    BitVec.toNat_sub_of_le (by change 1192 ≤ fr.rsp.toNat; omega)
  have srcNat : cf.rsi.toNat = fr.rsi.toNat+1 := by
    change (fr.rsi+1).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsi.toNat+1 < 2^64; omega)]
    rfl
  have win := e.window.of_frame frame
  have stack : Writable Extracted.programImage n (cf.rsp-1048) 1048 := by
    change Writable _ _ (fr.rsp-136-8-1048) _
    rw [show fr.rsp-136-8-1048 = fr.rsp-1192 by bv_omega]
    exact win.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _)
  have bottom : (fr.rsp-1192).toNat = fr.rsp.toNat-1192 := lowNat
  have slot : Readable n cf.rsp 8 := win.readable.sub (by omega) (by omega)
  have dst : Writable Extracted.programImage n cf.rdi 89 := win.sub (by omega) (by omega)
  have src : Readable n cf.rsi 32 := (e.input.of_frame frame).sub (by omega) (by omega)
  have pre : Compressed.EntryPre Extracted.programImage cf child n want :=
    ⟨congrArg (Value.get 64) regs.rsp,congrArg (Value.get 64) regs.rsi,congrArg (Value.get 64) regs.rdi,
     congrArg (fun v : Value => (v.get 64).setWidth 8) regs.rdx,
     congrArg (Value.get 64) (regs.saved 5 (by decide)),congrArg (Value.get 64) (regs.saved 3 (by decide)),
     congrArg (Value.get 64) (regs.saved 12 (by decide)),congrArg (Value.get 64) (regs.saved 13 (by decide)),
     congrArg (Value.get 64) (regs.saved 14 (by decide)),congrArg (Value.get 64) (regs.saved 15 (by decide)),
     regs.df,regs.saved 39 (by decide),regs.saved 50 (by decide),regs.saved 51 (by decide),
     ret,by change (0x1214ce : BitVec 64).toNat < 2^32; decide,slot,stack,by omega,by omega,src,dst,.inr (by omega)⟩
  have env : Compressed.Environment cf :=
    ⟨by have := e.text; omega, .inr (by omega)⟩
  have parity : want.toNat = t.toNat % 2 := by
    change ((if tag.toBitVec = 3 then (1 : BitVec 64) else 0).setWidth 8).toNat = (if tag = 5 then (2 : UInt8) else tag).toNat % 2
    rcases valid with rfl | rfl | rfl <;> decide
  have decoded' : Sec1.decompress t (Compressed.inputs n cf.rsi).x = some p := by
    change Sec1.decompress t (Compressed.inputs n (fr.rsi+1)).x = _
    rw [← e.coordinates frame size]
    exact decoded
  obtain ⟨out,run,returned,done_,_,writes,res⟩ :=
    compressedDecoder Common.fnCode_subset_programImage cf child n t want pre env parity decoded'
  have keeps := preservedAfterReturn regs done_
  have sp := done_.1
  have region : cf.region = (⟨(fr.rsp-136-8-1048).toNat,1048⟩ : MemoryRegion) := by
    rw [show fr.rsp-136-8-1048 = fr.rsp-1192 by bv_omega]
    change MemoryRegion.mk cf.low.toNat (cf.rsp.toNat-cf.low.toNat) = MemoryRegion.mk cf.low.toNat 1048
    rw [spNat,lowNat]
    exact congrArg (MemoryRegion.mk _) (by omega)
  rw [region] at writes
  refine ⟨out,run,returned,?_,keeps,writes,res⟩
  exact sp.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel (fr.rsp-136) 8))

end K256.Proofs.Ecdh.Decode.Affine
