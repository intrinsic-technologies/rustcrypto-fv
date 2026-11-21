import K256.Proofs.Sec1.Affine.Routines
import K256.Proofs.Sec1.Affine.Uncompressed.Contract

namespace K256.Proofs.Sec1.Affine

open K256.Spec.Program X86.Machine X86Proofs K256.Proofs.Refine K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR Standards.SECG.ECC

private theorem wordValue {s : RamState} {m : Ram} {bytes : ByteArray}
    (mem : CoordinateMemory s bytes m) (off : Nat) (fit : off + 32 ≤ bytes.size) :
    Encoding.octetsToNat (bytes.extract off (off+32)) =
      (Uncompressed.readCoordinate m ((activation s).rsi + BitVec.ofNat 64 off)).nat := by
  unfold Uncompressed.CoordinateWords.nat Uncompressed.CoordinateWords.limbs Uncompressed.readCoordinate
  rw [Uncompressed.unpack_value]
  simpa only [Common.scalarWord,Nat.reduceSub,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using mem.words off fit

theorem uncompressedRoutine {s : RamState} {bytes : ByteArray}
    (decoder : Uncompressed.DecoderCall Extracted.programImage)
    (header : bytes.data[0]? = some 4) (len : bytes.size = 65) : CoordinateRoutine s bytes 4 := by
  intro args m fr mem regs ret
  have geo := childGeometry mem (4 : BitVec 8)
  change fr.low.toNat + 1048 = fr.rsp.toNat ∧ fr.rsp.toNat + 8 = fr.rdi.toNat at geo
  have above : fr.rdi.toNat + 89 ≤ fr.rsi.toNat := mem.above
  have read : Readable m fr.rsi 64 := mem.input
  have y : fr.rdx = fr.rsi + 32 := by
    change (activation s).rsi + 33 = (activation s).rsi + 1 + 32; bv_omega
  have yn : fr.rdx.toNat = fr.rsi.toNat + 32 :=
    toNat_of_offsets y (addr_self fr.rsi) read.low (n := 32) (by decide)
  have width (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : args[i] = ⟨64,args[i].get 64⟩ := by
    have h := regs.saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;omega)
    rw [h]
    rcases i with ⟨i,hi'⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have stack : Writable Extracted.programImage m (fr.rsp-1048) 1048 := mem.stack
  have pre : Uncompressed.EntryPre Extracted.programImage args m fr.rsp fr.rdi fr.rsi fr.rdx fr.ret :=
    ⟨congrArg (Value.get 64) regs.rsp,congrArg (Value.get 64) regs.rdi,congrArg (Value.get 64) regs.rsi,
      congrArg (Value.get 64) regs.rdx,width,stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide),
      by omega,mem.slot,ret,by change (0x121502 : BitVec 64).toNat < 2^32; decide,mem.output,
      read.sub (Nat.le_refl _) (by omega),read.sub (by omega) (by omega),.inr (by omega),.inr (by omega),
      .inr (Nat.le_of_eq geo.2)⟩
  obtain ⟨out,run,tag,sp,_,keep,writes,flag,point⟩ := decoder args m _ _ _ _ _ pre
  have frame := (RamWriteFrame.refl m (coordinateWrites (activation s))).trans writes (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · have a : (fr.rsp-273).toNat = fr.rsp.toNat-273 := BitVec.toNat_sub_of_le (by change 273 ≤ fr.rsp.toNat; omega)
      refine ⟨_,List.mem_cons_self,?_,?_⟩
      · change fr.low.toNat ≤ (fr.rsp-273).toNat; omega
      · change (fr.rsp-273).toNat + 273 ≤ fr.low.toNat + 1048; omega
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩)
  refine ⟨out,run,tag,sp.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel ((activation s).rsp-136) (8 : BitVec 64))),
    fun i hi => keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;omega),frame,?_⟩
  have x : Encoding.octetsToNat (bytes.extract 1 33) = (Uncompressed.readCoordinate m fr.rsi).nat :=
    wordValue mem 1 (by omega)
  have y' : Encoding.octetsToNat (bytes.extract 33 65) = (Uncompressed.readCoordinate m fr.rdx).nat :=
    wordValue mem 33 (by omega)
  have spec := decodePublicKey_uncompressed len header
  rw [x,y'] at spec
  let p := Curve.Point.affine (Uncompressed.readCoordinate m fr.rsi).nat (Uncompressed.readCoordinate m fr.rdx).nat
  cases ok : Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain p with
  | false =>
    have none_ : K256.Spec.Secp256k1.decodePublicKey bytes = none := spec.trans (ite_eq_right (by change ¬ (Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain p = true); rw [ok]; decide))
    rw [none_]; change memLoad out.store (fr.rdi+88) 8 = 0
    exact flag.trans (congrArg (fun b : Bool => BitVec.ofNat 8 b.toNat) ok)
  | true =>
    have some_ : K256.Spec.Secp256k1.decodePublicKey bytes = some p := spec.trans (ite_eq_left ok)
    rw [some_]
    exact ⟨flag.trans (congrArg (fun b : Bool => BitVec.ofNat 8 b.toNat) ok),point ok⟩

end K256.Proofs.Sec1.Affine
