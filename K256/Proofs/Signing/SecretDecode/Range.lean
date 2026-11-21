import K256.Proofs.Signing.SecretDecode.Range.Compare
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Verify.Transfer.Compare
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

theorem rangePath {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106e35 fr a m)
    (words : ParseSignature.scalarLimbsAt m (fr.rsp - 80) fr.original fr.rsi)
    (valid : Generate.Sampling.orderFlag (word fr 0) (word fr 1) (word fr 2) (word fr 3) = 1) :
    ∃ b n, Verify.Core.Reaches .l106e35 a m .l106eed b n ∧ Frame .l106eed fr b n ∧ Limbs fr b := by
  obtain ⟨b,n,call,di,sp,limbs,keep,widths,written,ret⟩ := compareBlock room high h words valid
  have atoms := h.atoms
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,df,bx,bp,_,_,_,_,mx,ft,fc,s3,s12,s13,s14,s15,s5,rd,ret0,retLow,stack,space,align,_⟩ := atoms
  let base := {fr with
    original := n, low := fr.rsp - 129, rsp := fr.rsp - 128,
    ret := 0x106ee4, rbx := fr.rdi, r12 := word fr 2, r13 := word fr 3,
    r14 := word fr 0, r15 := word fr 1}
  let child := ParseSignature.withArguments base b
  have addr (k : Nat) (hk : k ≤ 336) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have kNat : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,kNat]; omega),kNat]
  have bottom : (fr.rsp - 336).toNat = fr.rsp.toNat - 336 := addr 336 (by decide)
  have top : child.rsp.toNat = fr.rsp.toNat - 128 := addr 128 (by decide)
  have floor : child.low.toNat = fr.rsp.toNat - 129 := addr 129 (by decide)
  have below : child.rsp - 1 = child.low := by change fr.rsp - 128 - 1 = fr.rsp - 129; bv_omega
  have stk := stack.of_frame written
  have read : Readable n child.rsp 8 := stk.readable.sub (by rw [bottom,top]; omega) (by rw [bottom,top]; omega)
  have write : Writable Extracted.programImage n (child.rsp - 1) 1 := by
    rw [below]
    exact stk.sub (by rw [bottom,floor]; omega) (by rw [bottom,floor]; omega)
  have entry : Atom.All Extracted.programImage b n (Generate.LIR.Fn127d50.frameAt .l127d50 child) := by
    simp only [Generate.LIR.Fn127d50.frameAt, Generate.LIR.Fn127d50.frameAtG10, Atom.All, Atom.Holds]
    refine ⟨sp,(keep 22 (by decide)).trans df,ParseSignature.entryArgument widths base 1 (by decide),
      ParseSignature.entryArgument widths base 2 (by decide),(keep 3 (by decide)).trans bx,
      (keep 5 (by decide)).trans bp,ParseSignature.entryArgument widths base 6 (by decide),
      ParseSignature.entryArgument widths base 7 (by decide),ParseSignature.entryArgument widths base 8 (by decide),
      ParseSignature.entryArgument widths base 9 (by decide),limbs.w2,limbs.w3,limbs.w0,limbs.w1,
      (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
      read,ret,by change (0x106ee4#64).toNat < 2^32; decide,write,?_,?_,trivial⟩
    · rw [floor,top]; omega
    · rw [top]; omega
  obtain ⟨out,exec,tag,regs,wbox,wout,value⟩ :=
    Generate.Generator.Sample.blackBox_call Common.fnCode_subset_programImage child b entry
  have reach := Verify.Core.Lincomb.reachesCall call (Verify.Transfer.compareExec (src := .l127d50) rfl exec) tag
  rw [← Generate.LIR.Fn127d50.doneAt_canonical] at regs
  simp only [Generate.LIR.Fn127d50.doneAt,Atom.All,Atom.Holds] at regs
  obtain ⟨osp,odf,obx,_,o12,o13,o14,o15,omx,oft,ofc,_⟩ := regs
  have ob : out.values[0] = ⟨64,1⟩ := by
    change out.values[0] = ⟨64,((b[7].get 64).setWidth 8).zeroExtend 64⟩ at value
    rw [di] at value
    exact value
  have off : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := top
  have writes : RamWriteFrame m out.store [⟨(fr.rsp - 129).toNat,17⟩] := by
    apply ((RamWriteFrame.refl m _).trans written ?_).trans wbox
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_singleton_self _,by change (fr.rsp - 129).toNat ≤ child.low.toNat; exact Nat.le_refl _,
        by change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ (fr.rsp - 129).toNat + 17
           change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ child.low.toNat + 17
           rw [floor,top]; omega⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      · change child.low.toNat ≤ (fr.rsp - 128).toNat
        rw [floor,off]; omega
      · change (fr.rsp - 128).toNat + 16 ≤ child.low.toNat + 17
        rw [floor,off]; omega
  have total := h.writes.trans writes (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region,List.mem_singleton_self _,?_,?_⟩
    · change fr.low.toNat ≤ child.low.toNat
      rw [low,bottom,floor]; omega
    · change child.low.toNat + 17 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      rw [low,bottom,floor]; omega)
  have saved (k : Nat) (hk : k ≤ 48) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply writes.memLoad_eq
    refine ⟨by rw [addr k (by omega)]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change child.low.toNat + 17 ≤ _
    rw [floor,addr k (by omega)]; omega
  have sameRet : memLoad out.store fr.rsp 64 = fr.ret := by
    have z := saved 0 (by decide)
    rw [show fr.rsp - BitVec.ofNat 64 0 = fr.rsp from BitVec.sub_zero _] at z
    exact z.trans ret0
  have rsp : out.values[4] = ⟨64,fr.rsp - 120⟩ := by
    refine osp.trans (congrArg (Value.mk 64) ?_)
    change fr.rsp - 128 + 8 = fr.rsp - 120
    bv_omega
  refine ⟨?c,out.store,reach.trans (Semantics.Reaches.single ?run),⟨?atoms,total,?widths⟩,?limbs⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval
    have zf : (cmpSpec ((out.values[0].get 64).setWidth 8) (1#8)).ZF = true := by rw [ob]; rfl
    split
    · rename_i cond
      exact False.elim (Bool.noConfusion (show false = true from (congrArg Bool.not zf).symm.trans cond))
    · rfl
  case atoms =>
    simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds]
    exact ⟨rsp,odf,obx,omx,oft,ofc,(saved 48 (by decide)).trans s3,(saved 40 (by decide)).trans s12,
      (saved 32 (by decide)).trans s13,(saved 24 (by decide)).trans s14,
      (saved 16 (by decide)).trans s15,(saved 8 (by decide)).trans s5,rd.of_frame writes,
      sameRet,retLow,stack.of_frame writes,space,align,trivial⟩
  case widths =>
    rintro ⟨i,hi⟩ mem
    have eq := wout ⟨i,hi⟩ mem
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> exact eq
  case limbs => exact ⟨o14,o15,o12,o13,rfl⟩

end K256.Proofs.Signing.SecretDecode
