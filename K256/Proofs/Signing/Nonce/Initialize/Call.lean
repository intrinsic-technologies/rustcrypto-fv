import K256.Proofs.Signing.Nonce.Initialize.Call.Setup
import K256.Proofs.Signing.Nonce.Initialize.Update

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem seedUpdate {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {d : Nat} {digest : ByteArray}
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (dst : fr.rdi = fr.rsp + 712) (secretPtr : fr.rsi = fr.rsp + 32)
    (digestPtr : fr.rcx = fr.rsp + 376)
    (secretLen : fr.rdx = 32) (digestLen : fr.r8 = 32) (extraPtr : fr.r9 = 1)
    (extraLen : memLoad fr.original (fr.rsp + 8) 64 = 0)
    (orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616)
    (secret : (⟨fr.rsi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original (Encoding.natToOctets 32 d))
    (len : digest.size = 32) (ready : Prepared fr a m digest) :
    ∃ b n, Verify.Core.Reaches .l101295 a m .l10132a b n ∧ Updated fr b n (initial d digest) := by
  obtain ⟨b,n,call,entry,stage,slices,bytes⟩ := setup image depth low limit window dst secretPtr
    digestPtr secretLen digestLen extraPtr extraLen orderPtr secret ready
  let child := updateActivation fr a n
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, _, _, _, _, _, _, sx, sl, ss, sd, sbx, s12, s13, s14, s15, sbp, rd, ret,
    retL, win, space, align, _⟩ := atoms
  have sub (k : BitVec 64) (hk : k.toNat ≤ 2208) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have base : fr.low.toNat = fr.rsp.toNat - 2208 := by rw [low,sub _ (by decide)]; rfl
  have lower : RegionsWithin [⟨(fr.rsp - 288).toNat,160⟩] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp only [Activation.region,base,sub _ (by decide : (288 : BitVec 64).toNat ≤ 2208),
      BitVec.reduceToNat]
    omega
  have staged := ready.writes.trans stage lower
  have preserved : ∀ v ∈ Extracted.programImage, n[v.1]? = some v.2 := by
    intro v hv
    apply (staged.outside _ ⟨by have := v.1.isLt; omega, ?_⟩).trans (image v hv)
    intro reg member
    obtain rfl := List.mem_singleton.mp member
    change v.1.toNat + 1 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    apply Classical.byContradiction
    intro hn
    have avoid := win.notCode v hv (v.1.toNat - fr.low.toNat) (by omega)
    apply avoid
    rw [← low, ← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have childDepth : 1920 ≤ child.rsp.toNat := by change 1920 ≤ (fr.rsp - 288).toNat; simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have floor : child.low = child.rsp - 1920 := by
    change fr.low = fr.rsp - 288 - 1920
    rw [low]; bv_omega
  have top : child.rsp.toNat + 8 < 2^32 := by change (fr.rsp - 288).toNat + 8 < _; simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have addrLow : child.rdi.toNat + 64 < 2^32 := by change (fr.rsp - 272).toNat + 64 < _; simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have outside : child.rsp.toNat + 8 ≤ child.rdi.toNat := by
    change (fr.rsp - 288).toNat + 8 ≤ (fr.rsp - 272).toNat
    simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  have writable : Writable Extracted.programImage n child.rdi 64 := by
    apply (win.of_frame stage).sub
    all_goals change _ ≤ _; dsimp only [child,updateActivation]; simp (disch := decide) only [sub, BitVec.reduceToNat] <;> omega
  obtain ⟨out,run,tag,done_,widths,writes,keyValue⟩ := update entry preserved childDepth floor top addrLow
    (.inr outside) writable slices bytes
  have called := Verify.reachesOfCall call run tag
  have saved (k : BitVec 64) (hk : k.toNat ≤ 176) :
      memLoad out.store (fr.rsp - k) 64 = memLoad n (fr.rsp - k) 64 := by
    apply writes.memLoad_eq
    refine ⟨by rw [sub _ (by omega)]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;>
      simp (disch := first | omega | decide) only [updateActivation,Activation.region,base,sub,BitVec.reduceToNat] <;> omega
  have old (k : BitVec 64) (hk : k.toNat ≤ 112) :
      memLoad out.store (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    refine (saved k (by omega)).trans (stage.memLoad_eq ?_)
    refine ⟨by rw [sub _ (by omega)]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp - 288).toNat + 160 ≤ (fr.rsp - k).toNat
    simp (disch := first | omega | decide) only [sub, BitVec.reduceToNat]
    omega
  have total := staged.trans writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases hr with rfl | rfl <;>
      simp (disch := first | omega | decide) only [updateActivation,Activation.region,base,sub,BitVec.reduceToNat] <;> omega)
  have rt := old 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp from BitVec.sub_zero _] at rt
  have input := slices
  simp only [Input.At,updateActivation,reduceAddOffset] at input
  obtain ⟨_,_,_,_,_,s0,s1,_,s3,s4,_⟩ := input
  simp only [Fn103f30.doneAt,Atom.All,Atom.Holds,updateActivation] at done_
  obtain ⟨sp,df,bx,_,_,_,di,order,mx,ft,fc,_⟩ := done_
  have parentSp := sp.trans (congrArg (Value.mk 64) (show fr.rsp - 288 + 8 = fr.rsp - 280 by bv_omega))
  refine ⟨out.values, out.store, called, ⟨⟨?_,total⟩,order,?_,widths⟩⟩
  · simp only [Fn100ea0.frameAt,Fn100ea0.frameAtG1,Atom.All,Atom.Holds]
    refine ⟨parentSp,df,bx,di,mx,ft,fc, (saved _ (by decide)).trans (s0.trans secretPtr.symm),
      (saved _ (by decide)).trans (s1.trans secretLen.symm), (saved _ (by decide)).trans (s3.trans secretLen.symm),
      (saved _ (by decide)).trans (s4.trans extraPtr.symm),
      (old _ (by decide)).trans sx,(old _ (by decide)).trans sl,(old _ (by decide)).trans ss,
      (old _ (by decide)).trans sd,(old _ (by decide)).trans sbx,(old _ (by decide)).trans s12,
      (old _ (by decide)).trans s13,(old _ (by decide)).trans s14,(old _ (by decide)).trans s15,
      (old _ (by decide)).trans sbp, (rd.of_frame stage).of_frame writes,rt.trans ret,retL,
      (win.of_frame stage).of_frame writes,space,align,trivial⟩
  · rw [initial,Drbg.initialState_eq d digest len]
    exact keyValue

end K256.Proofs.Signing.Nonce.Initialize
