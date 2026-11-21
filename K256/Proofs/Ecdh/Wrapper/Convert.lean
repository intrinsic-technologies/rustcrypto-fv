import K256.Proofs.Ecdh.Wrapper.Convert.Call
import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Ecdh.Decode.Convert
import K256.Proofs.Ecdh.Scalar.Calls
import K256.Proofs.Ecdh.Scalar.Child
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

set_option maxRecDepth 4096 in
theorem convertPeer {s : RamState} {secret key : ByteArray} {d : Nat} {p : Curve.Point}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (scalar : ScalarAt s m 0x10 d)
    (source : Decode.AffinePointAt m (localSp s + 0x158) p) (valid : Curve.onCurve domain p = true) :
    ∃ b n, ∃ peer : Generate.Generator.Multiply.Projective, Reaches .l101831 a m .l10185f b n ∧ Caller s b n ∧
      b[15] = ⟨64, localSp s + 0x158⟩ ∧ ScalarAt s n 0x10 d ∧
      peer.Stored n (localSp s + 0x158) ∧ peer.valid ∧ peer.value = p := by
  let sp := localSp s
  let src := sp + 344
  let dst := sp + 4184
  let copied := memCopy m dst src 88
  let pushed := memStore copied (returnSlot s) (0x10185f : BitVec 64)
  obtain ⟨room,high,base⟩ := Scalar.stack_geometry call
  change sp.toNat = _ at base
  have addr (k : Nat) (hk : k ≤ 6152) :
      (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := k) (by omega),Nat.mod_eq_of_lt (by omega)]
  have sn : src.toNat = sp.toNat + 344 := addr 344 (by decide)
  have dn : dst.toNat = sp.toNat + 4184 := addr 4184 (by decide)
  have code := fun x hx => Common.fnCode_subset_programImage x (code_l101831 x hx)
  have win := state.toMemory.window call
  have read : Readable m src 88 := win.readable.of_offsets rfl (addr_sub _ _) (by decide)
  have write : Writable Extracted.programImage m dst 88 := win.of_offsets rfl (addr_sub _ _) (by decide)
  have store : StoreOk Extracted.programImage m dst 88 0x101849 3 :=
    ParseSignature.storeOk_of_codeRange (off := 24) write code (by decide)
  have copy : RepMovsOk Extracted.programImage m 0 src dst 11 8 0x101849 3 :=
    Generate.Generator.Multiply.Prepare.copyGuard read store (Or.inl (by change src.toNat + 88 ≤ dst.toNat; omega))
  have cf : RamWriteFrame m copied [⟨dst.toNat,88⟩] := Sec1.Wrapper.Copy.memCopy_frame
    (RamWriteFrame.refl _ _) ⟨_,List.mem_singleton_self _,Nat.le_refl _,Nat.le_refl _,by omega⟩
  have cm := state.toMemory.advance call cf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ dst.toNat ∧ dst.toNat + 88 ≤ _
    omega)
  obtain ⟨push,pm,pf,ret,apart⟩ := callSite call cm 6160 (by decide) (by decide)
    0x101831 bytes_l101831 41 5 code (by decide) (0x10185f : BitVec 64)
  obtain ⟨b,block,regs,bx,bsi,bdi,b15⟩ := convertCall state copy push
  let fr := childActivation s pushed b 97 0x10185f
  have entry := Scalar.childEntry call pm.frame regs Fn10fa10.frameInfo rfl (by decide)
    (by decide) (by decide : (0x10185f : BitVec 64).toNat < 2^32) ret
  have hsi : fr.rsi = dst := by change b[6].get 64 = dst; rw [bsi]; rfl
  have hdi : fr.rdi = src := by change b[7].get 64 = src; rw [bdi]; rfl
  have lo : fr.low.toNat = (stackPtr s).toNat - 6257 :=
    Common.stackOffset call.stackAvailable (off := 6257) (by decide)
  have top : fr.rsp.toNat = (stackPtr s).toNat - 6160 :=
    Common.stackOffset call.stackAvailable (off := 6160) (by decide)
  have srcApart : Outside [ParseSignature.callStack fr] dst 84 := by
    simp only [Outside,List.mem_singleton,forall_eq,ParseSignature.callStack,lo,top]
    change dst.toNat + 84 ≤ _ ∧ _
    exact ⟨by omega,Or.inr (by change _ ≤ dst.toNat; omega)⟩
  have dstApart : Outside [ParseSignature.callStack fr] src 120 := by
    simp only [Outside,List.mem_singleton,forall_eq,ParseSignature.callStack,lo,top]
    change src.toNat + 120 ≤ _ ∧ _
    exact ⟨by omega,Or.inr (by change _ ≤ src.toNat; omega)⟩
  have beforePush : Outside [⟨(returnSlot s).toNat,8⟩] dst 88 := by
    have eq : dst = stackPtr s - 1968 := localOffset s 4184 (by decide)
    rw [eq]
    exact apart 1968 88 (by decide) (by decide)
  have pushedFrame : RamWriteFrame copied pushed [⟨(returnSlot s).toNat,8⟩] := pf
  have input : Decode.AffinePointAt pushed dst p := by
    apply source.of_copy
    intro k w hk
    refine (pushedFrame.memLoad_eq ?_).trans (Sec1.Parser.Result.memLoad_memCopy m dst src (by decide) hk)
    apply Generate.Generator.Affine.outside_subregion beforePush
    all_goals
      have off : (dst + BitVec.ofNat 64 k).toNat = dst.toNat + k := by
        simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := k) (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
  have w' := pm.window call
  obtain ⟨out,run,tag,done_,writes,widths,peer,stored,pvalid,pval⟩ :=
    Decode.Convert.execution fr b entry
      (hsi ▸ w'.readable.of_offsets (show dst = sp + 4184 from rfl) (addr_sub _ _) (by decide))
      (hsi ▸ srcApart) (hdi ▸ w'.of_offsets (show src = sp + 344 from rfl) (addr_sub _ _) (by decide))
      (hdi ▸ dstApart) (hsi ▸ input) valid
  have ⟨rsp,keep⟩ := Scalar.childReturn (win := 97) (ret := 0x10185f) (m := pushed) regs done_
  have finalMem := pm.advance call writes (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · change _ ≤ fr.low.toNat ∧ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp hr
      change _ ≤ fr.rdi.toNat ∧ fr.rdi.toNat + 120 ≤ _
      rw [hdi]
      omega)
  have finalRegs : Caller s out.values out.store := by
    refine ⟨finalMem,rsp,(keep 3 (by decide)).trans bx,(keep 22 (by decide)).trans regs.df,
      ?_,?_,?_,?_⟩
    · intro i hi
      by_cases arg : i.val ∈ Activation.argumentNumbers
      · exact widths i arg
      · rw [keep i (by simp only [Generate.Generator.Sample.nonzeroPreserved,
          Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at *; omega)]
        exact regs.gp i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)
    · exact (congrArg Value.width (keep 39 (by decide))).trans regs.mxcsr
    · exact (congrArg Value.width (keep 50 (by decide))).trans regs.ftw
    · exact (congrArg Value.width (keep 51 (by decide))).trans regs.fcw
  refine ⟨out.values,out.store,peer,Scalar.resumeCall block run tag,finalRegs,
    (keep 15 (by decide)).trans b15,?_,by rwa [hdi] at stored,pvalid,pval⟩
  have near : (sp + 16).toNat = sp.toNat + 16 := addr 16 (by decide)
  have preserved : ScalarAt s copied 16 d := by
    apply scalar.of_frame cf (by decide)
    change Outside [⟨dst.toNat,88⟩] (sp + 16) 32
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change _ ≤ dst.toNat; omega)
  have atCall : ScalarAt s pushed 16 d := by
    apply preserved.of_frame pushedFrame (by decide)
    rw [localOffset s 16 (by decide)]
    exact apart 6136 32 (by decide) (by decide)
  apply atCall.of_frame writes (by decide)
  change Outside [fr.region, ⟨fr.rdi.toNat,120⟩] (sp + 16) 32
  refine ⟨by omega,fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    omega
  · obtain rfl := List.mem_singleton.mp hr
    left
    change _ ≤ fr.rdi.toNat
    rw [hdi]
    omega

end K256.Proofs.Ecdh.Wrapper
