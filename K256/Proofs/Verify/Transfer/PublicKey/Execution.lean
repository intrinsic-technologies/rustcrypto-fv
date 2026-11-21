import K256.Proofs.Verify.Transfer.PublicKey.Uncompressed
import K256.Proofs.Verify.Transfer.PublicKey.Affine
import K256.Proofs.Verify.Transfer.PublicKey.Return

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR Standards.SECG.ECC

theorem execution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn106390.frameAt .l106390 fr))
    (len : fr.rdx = 65) (src : Readable fr.original fr.rsi 65)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 65)
    (dst : Writable Extracted.programImage fr.original fr.rdi 96)
    (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (image : ∀ x ∈ Extracted.programImage, fr.original[x.1]? = some x.2)
    (text : fr.rsp.toNat ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat - 1544)
    {bytes : ByteArray} {point : Curve.Point} (size : bytes.size = 65)
    (bytesAt : (⟨fr.rsi.toNat,65⟩ : MemoryRegion).HasBytes fr.original bytes)
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106390,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn106390.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,96⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧ memLoad out.store fr.rdi 64 = 0 ∧
      Ecdh.Decode.AffinePointAt out.store (fr.rdi+8) point := by
  have head := uncompressedTag size decoded
  obtain ⟨b,m,path,e,slots,packed⟩ := pack fr a entry len src srcApart image text size head bytesAt
  obtain ⟨c,run,ret,rsp,keep,writes,flag,pointAt,widths⟩ := affine e size head decoded
  have resume := ParseSignature.exec_reaches_resume run Sec1.Parser.Packing.affineResume []
    (by rw [ret]; rfl)
  have args := ParseSignature.resume_arguments Sec1.Parser.Packing.affineResume c
  dsimp only [StackFrame.resume] at args
  simp only [List.nil_append, StackFrame.resume, args] at resume
  simp only [Fn106390.frameAt,Fn106390.frameAtG0,Atom.All,Atom.Holds] at entry
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,slot,_,retLow,stack,room,_⟩ := entry
  change fr.low.toNat+1544 ≤ fr.rsp.toNat at room
  have geom (k : BitVec 64) (hk : k.toNat ≤ 1544) :
      (fr.rsp-k).toNat = fr.rsp.toNat-k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have bottom : ((affineFrame fr m).rsp-1192).toNat = fr.rsp.toNat-1544 := by
    change (fr.rsp-344-8-1192).toNat = _
    rw [BitVec.sub_sub,BitVec.sub_sub]
    exact geom _ (by decide)
  have dest : (affineFrame fr m).rdi.toNat = fr.rsp.toNat-184 := by
    change (fr.rsp-344+160).toNat = _
    rw [show fr.rsp-344+160 = fr.rsp-184 by bv_omega]
    exact geom _ (by decide)
  have contained : RegionsWithin (Ecdh.Decode.Affine.writes (affineFrame fr m)) [fr.region] := by
    intro r hr
    simp only [Ecdh.Decode.Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    all_goals refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;>
      dsimp only [Activation.region] <;> omega
  have apart {p : BitVec 64} {n : Nat} (low : p.toNat+n ≤ 2^64)
      (left : fr.rsp.toNat-352 ≤ p.toNat)
      (right : p.toNat+n ≤ fr.rsp.toNat-184 ∨ fr.rsp.toNat-95 ≤ p.toNat) :
      Outside (Ecdh.Decode.Affine.writes (affineFrame fr m)) p n := by
    refine ⟨low,fun r hr => ?_⟩
    simp only [Ecdh.Decode.Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  have old (k : BitVec 64) (hk : k.toNat ≤ 32) :
      memLoad c.store (fr.rsp-k) 64 = memLoad m (fr.rsp-k) 64 := by
    apply writes.memLoad_eq
    have atK := geom k (by omega)
    have bound := slot.low
    apply apart <;> omega
  obtain ⟨s3,s12,s14,s15,sret⟩ := slots
  have retEq := old 0 (by decide)
  rw [show fr.rsp-(0 : BitVec 64) = fr.rsp by bv_omega] at retEq
  have saved' : saved fr c.store := ⟨(old 32 (by decide)).trans s3,(old 24 (by decide)).trans s12,
    (old 16 (by decide)).trans s14,(old 8 (by decide)).trans s15,
    retEq.trans sret⟩
  have srcN : (fr.rsp-344+4).toNat = fr.rsp.toNat-340 := by
    rw [show fr.rsp-344+4 = fr.rsp-340 by bv_omega]
    exact geom _ (by decide)
  have htag : memLoad c.store (fr.rsp-344+4) 8 = 4 := by
    rw [writes.memLoad_eq (apart (by have := fr.rsp.isLt; change _+1 ≤ _; omega)
      (by omega) (.inl (by change _+1 ≤ _; omega))),memLoad_8]
    have ht := e.bytesAt 0 (by decide)
    simp only [BitVec.add_zero,head,Option.getD_some] at ht
    exact congrArg UInt8.toBitVec ht
  have regs (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,39,50,51]) :
      c.values[i] = (affineFrame fr m).entryValue i.val :=
    (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (e.saved i hi)
  have stable (i : Fin Reg.count) (hi : i.val ∈ [5,13,39,50,51]) : c.values[i] = fr.entryValue i.val := by
    refine (regs i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans ?_
    obtain ⟨i,lt⟩ := i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl
  have crsp : c.values[4] = ⟨64,fr.rsp-344⟩ := by
    simpa only [affineFrame,BitVec.sub_add_cancel] using rsp
  obtain ⟨out,last,post⟩ := finish fr (packed.trans writes contained) stack room slot retLow saved' dst dstAbove
    crsp (regs 3 (by decide)) (regs 12 (by decide)) (regs 15 (by decide))
    ((keep 22 (by decide)).trans e.df) stable widths htag flag pointAt
  exact ⟨out,Program.Exec.of_sem (path.exec (resume.exec last.sem)), post⟩

end K256.Proofs.Verify.Transfer.PublicKey
