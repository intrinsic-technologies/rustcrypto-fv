import K256.Proofs.Sec1.Affine.Routines
import K256.Proofs.Sec1.Affine.Compressed.Contract
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR Standards.SECG.ECC

private theorem childText {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (m : Ram) (t : BitVec 8) : let fr := childActivation s m t
    fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat := by
  have write := Wrapper.stackWritable (offset := 1928) (len := 1936) call (by decide) (by decide) (by decide)
  have text := Serialize.writable_text_apart write (by decide)
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  change (s.regValue .rsp - 1928).toNat + 1936 ≤ 0x100000 ∨ 0x12a9bf ≤ (s.regValue .rsp - 1928).toNat at text
  rw [rootStackOffset call 1928 (by decide)] at text
  change _ - 1928 + 1936 ≤ 0x100000 ∨ 0x12a9bf ≤ (s.regValue .rsp).toNat - 1928 at text
  dsimp only [childActivation,activation]
  rw [show s.regValue .rsp - 600 - 8 - 136 - 8 - 1048 = s.regValue .rsp-1800 by bv_omega,
    show s.regValue .rsp - 600 - 8 - 136 - 8 = s.regValue .rsp-752 by bv_omega,
    rootStackOffset call 1800 (by decide),rootStackOffset call 752 (by decide)]
  change (s.regValue .rsp).toNat - 752 + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ (s.regValue .rsp).toNat - 1800
  omega

private theorem wantParity {tag : UInt8} (valid : tag = 2 ∨ tag = 3 ∨ tag = 5) :
    ((if tag.toBitVec = 3 then (1 : BitVec 64) else 0).setWidth 8).toNat =
      (if tag = 5 then (2 : UInt8) else tag).toNat % 2 := by
  rcases valid with rfl | rfl | rfl <;> decide

private theorem compressedSpec {bytes : ByteArray} {tag : UInt8}
    (valid : tag = 2 ∨ tag = 3 ∨ tag = 5) (header : bytes.data[0]? = some tag)
    (len : bytes.size = 33) : K256.Spec.Secp256k1.decodePublicKey bytes =
      Sec1.decompress (if tag = 5 then 2 else tag) (Encoding.octetsToNat (bytes.extract 1 33)) := by
  rcases valid with rfl | rfl | rfl
  · exact decodePublicKey_compressed len header (Or.inl rfl)
  · exact decodePublicKey_compressed len header (Or.inr rfl)
  · exact decodePublicKey_compact len header

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

theorem compressedRoutine {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (decoder : Compressed.DecoderCall Extracted.programImage) {tag : UInt8}
    (valid : tag = 2 ∨ tag = 3 ∨ tag = 5) (header : bytes.data[0]? = some tag)
    (len : bytes.size = 33) : CoordinateRoutine s bytes tag.toBitVec := by
  intro args m fr
  let t := if tag = 5 then (2 : UInt8) else tag
  let want := fr.rdx.setWidth 8
  intro mem regs ret
  have geo := childGeometry mem tag.toBitVec
  change fr.low.toNat + 1048 = fr.rsp.toNat ∧ fr.rsp.toNat + 8 = fr.rdi.toNat at geo
  have above : fr.rdi.toNat + 89 ≤ fr.rsi.toNat := mem.above
  have room : 1048 ≤ fr.rsp.toNat := mem.room
  have useCompressed : (tag.toBitVec != 4) = true := by rcases valid with rfl | rfl | rfl <;> decide
  have retLow : fr.ret.toNat < 2^32 := by
    change (if tag.toBitVec != 4 then (0x1214ce : BitVec 64) else 0x121502).toNat < 2^32
    rw [ite_eq_left useCompressed]; decide
  have input : Readable m fr.rsi 64 := mem.input
  have pre : Compressed.EntryPre Extracted.programImage fr args m want :=
    ⟨congrArg (Value.get 64) regs.rsp,congrArg (Value.get 64) regs.rsi,congrArg (Value.get 64) regs.rdi,
     congrArg (fun v : Value => (v.get 64).setWidth 8) regs.rdx,
     congrArg (Value.get 64) (regs.saved 5 (by decide)),congrArg (Value.get 64) (regs.saved 3 (by decide)),
     congrArg (Value.get 64) (regs.saved 12 (by decide)),congrArg (Value.get 64) (regs.saved 13 (by decide)),
     congrArg (Value.get 64) (regs.saved 14 (by decide)),congrArg (Value.get 64) (regs.saved 15 (by decide)),
     regs.df,regs.saved 39 (by decide),regs.saved 50 (by decide),regs.saved 51 (by decide),
     ret,retLow,mem.slot,mem.stack,(Nat.le_of_eq geo.1),mem.aligned,
     input.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide) _),mem.output,.inr (by omega)⟩
  have txt := childText call m tag.toBitVec
  change fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat at txt
  have env : Compressed.Environment fr := ⟨by omega,.inr (Nat.le_of_eq geo.2)⟩
  have parity : want.toNat = t.toNat % 2 := by
    change ((if tag.toBitVec != 4 then (if tag.toBitVec = 3 then (1 : BitVec 64) else 0) else _).setWidth 8).toNat = _
    rw [ite_eq_left useCompressed]
    exact wantParity valid
  obtain ⟨out, run, tagOut, done_, _, writes, res⟩ := decoder fr args m t want pre env parity
  have spec := compressedSpec valid header len
  have x : Encoding.octetsToNat (bytes.extract 1 33) = (Compressed.inputs m fr.rsi).x := by
    have h := mem.words 1 (by omega)
    dsimp only [Compressed.Inputs.x, Compressed.inputs, Uncompressed.CoordinateWords.nat,
      Uncompressed.CoordinateWords.limbs, Uncompressed.readCoordinate]
    rw [Uncompressed.unpack_value,show fr.rsi = (activation s).rsi + 1 from rfl]
    simpa only [Common.scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] using h
  have keeps := preservedAfterReturn regs done_
  simp only [Fn1205b0.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨sp,df,bx,_,_,r13,_,_,mx,ft,fc,_⟩ := done_
  have fregion : fr.region = (⟨fr.low.toNat,1048⟩ : MemoryRegion) := by
    change MemoryRegion.mk _ _ = MemoryRegion.mk _ _
    exact congrArg (MemoryRegion.mk fr.low.toNat) (by change fr.rsp.toNat - fr.low.toNat = 1048; omega)
  rw [fregion] at writes
  refine ⟨out,?_,tagOut,?_,?_,writes,?_⟩
  · exact (congrArg (fun l : Label => program.Exec (dialect Extracted.programImage) ⟨⟨l,args,m⟩,[]⟩ out)
      (show (if tag.toBitVec != 4 then Label.l1205b0 else .l11f780) = .l1205b0 from ite_eq_left useCompressed)).mpr run
  · exact sp.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel ((activation s).rsp-136) (8 : BitVec 64)))
  · exact keeps
  · have eq : K256.Spec.Secp256k1.decodePublicKey bytes = decompress t (Compressed.inputs m fr.rsi).x :=
      spec.trans (congrArg (decompress t) x)
    cases h : decompress t (Compressed.inputs m fr.rsi).x with
    | none =>
      rw [h] at res
      rw [eq.trans h]
      exact res
    | some p =>
      rw [h] at res
      rw [eq.trans h]
      exact res

end K256.Proofs.Sec1.Affine
