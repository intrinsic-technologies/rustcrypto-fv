import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Staging
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Return
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem mul : MulExecution := by
  intro fr a m x y atoms image _ hx hy rx ry output above apart wx wy
  obtain ⟨b,n,call,s⟩ := stageMul atoms rx ry (fun p hp => (apart p hp).1) wx wy
  let child := reductionActivation fr b n
  simp only [Fn1099c0.frameAt, Fn1099c0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,retRead,ret,retLow,stack,room,align,_⟩ := atoms
  have high := retRead.low
  have sub (k : Nat) (hk : k ≤ 321) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have modK : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, modK]; omega), modK]
  have n321 : (fr.rsp - 321).toNat = fr.rsp.toNat - 321 := sub 321 (by decide)
  have n192 : child.rsp.toNat = fr.rsp.toNat - 192 := sub 192 (by decide)
  have n112 : child.rsi.toNat = fr.rsp.toNat - 112 := sub 112 (by decide)
  have childImage : ∀ v ∈ Extracted.programImage, n[v.1]? = some v.2 := by
    intro v hv
    apply (s.frame.outside v.1 ?_).trans (image v hv)
    refine ⟨by have := v.1.isLt; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change v.1.toNat + 1 ≤ fr.rsp.toNat - 321 ∨ fr.rsp.toNat - 321 + 321 ≤ v.1.toNat
    apply Classical.byContradiction
    intro hn
    apply stack.notCode v hv (v.1.toNat - (fr.rsp - 321).toNat) (by omega)
    rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have wn := stack.of_frame s.frame
  have input : Readable n child.rsi 64 := wn.readable.sub (by omega) (by omega)
  obtain ⟨mid,childRun,tag,done_,widths,words,written⟩ :=
    reduceWide s.entry childImage rfl input (output.of_frame s.frame) (by change child.rsp.toNat + 8 ≤ child.rsi.toNat; omega)
      (by change child.rsi.toNat + 64 ≤ fr.rdi.toNat; omega) s.words
  change RamWriteFrame n mid.store [⟨child.rsp.toNat - 129,129⟩,⟨fr.rdi.toNat,32⟩] at written
  have total : RamWriteFrame m mid.store [mulStack fr, ⟨fr.rdi.toNat,32⟩] := by
    apply ((RamWriteFrame.refl m _).trans s.frame ?_).trans written
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨mulStack fr, List.mem_cons_self, ?_, ?_⟩
        · change fr.rsp.toNat - 321 ≤ child.rsp.toNat - 129
          omega
        · change child.rsp.toNat - 129 + 129 ≤ fr.rsp.toNat - 321 + 321
          omega
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have saved (k r : Nat) (small : k ≤ 48)
      (h : (k,r) ∈ [(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)]) :
      memLoad mid.store (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
    apply (written.memLoad_eq ?_).trans (s.saved k r h)
    rw [Outside, sub k (by omega)]
    refine ⟨by omega, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · right; change child.rsp.toNat - 129 + 129 ≤ _; omega
    · left; change _ + 8 ≤ fr.rdi.toNat; omega
  have ret' : memLoad mid.store fr.rsp 64 = fr.ret := by
    apply (total.memLoad_eq ?_).trans ret
    refine ⟨by omega, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · right; change fr.rsp.toNat - 321 + 321 ≤ _; omega
    · left; exact above
  simp only [Fn11b510.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨sp,df,_,_,_,_,r14,_,mx,ftw,fcw,_⟩ := done_
  have resume : Atom.All Extracted.programImage mid.values mid.store (Fn1099c0.frameAt .l109be7 fr) := by
    refine ⟨?_,df,r14,mx,ftw,fcw, saved 48 3 (by decide) (by decide), saved 40 12 (by decide) (by decide),
      saved 32 13 (by decide) (by decide), saved 24 14 (by decide) (by decide),
      saved 16 15 (by decide) (by decide), saved 8 5 (by decide) (by decide), retRead.of_frame total,
      ret', retLow, stack.of_frame total, room, align, trivial⟩
    change mid.values[4] = ⟨64,fr.rsp - 184⟩
    apply sp.trans
    congr 1
    change fr.rsp - 192 + 8 = fr.rsp - 184
    bv_omega
  obtain ⟨out,finish,returned,store,final,wide⟩ := mulReturn resume widths
  refine ⟨out, ParseSignature.exec_call call childRun ?_ ?_, returned, store.symm ▸ final,
    wide, ?_, store.symm ▸ total⟩
  · rw [tag]; rfl
  · change program.Exec _ ⟨⟨.l109be7,(Generator.callFrame .l109be7 0x109be7 |>.resume mid).arguments,mid.store⟩, []⟩ out
    rw [ParseSignature.resume_arguments]
    exact finish
  · rw [store]
    have hn : domain.n < 2^256 := by decide +kernel
    simpa only [reductionActivation, reduced_product (Nat.lt_trans hx hn) (Nat.lt_trans hy hn)] using words

end K256.Proofs.Generate.Generator.Multiply.Split
