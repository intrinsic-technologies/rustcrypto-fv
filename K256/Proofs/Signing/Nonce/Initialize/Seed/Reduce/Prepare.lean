import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.Subtract
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

private theorem stagedWrites (m : Ram) (sp : BitVec 64) (x : Nat)
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32) :
    RamWriteFrame m (digestStage m sp x) [⟨(sp - 288).toNat,176⟩] := by
  unfold digestStage
  have inside (k : BitVec 64) (hk : k.toNat ≤ 288) (hb : 120 ≤ k.toNat) :
      InRegions [⟨(sp - 288).toNat,176⟩] (sp - k) 8 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    dsimp only [InRegion]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 288 ≤ sp.toNat; omega)),
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    change sp.toNat - 288 ≤ _ ∧ _ ≤ sp.toNat - 288 + 176 ∧ _
    omega
  repeat' (apply RamWriteFrame.memStore; rotate_left; exact inside _ (by decide) (by decide))
  exact .refl _ _

private theorem stagedWords (m : Ram) (sp : BitVec 64) (x : Nat) :
    WordsAt (digestStage m sp x) (sp - 176) 64 (scalarWords x) ∧
    WordsAt (digestStage m sp x) (sp - 272) 64
      (Common.Invert.ModularShift.words (digestDifference x).1) := by
  constructor <;> intro i hi <;>
    obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, Lift.reduceAddOffset]
    unfold digestStage
    segment_words [] <;> rfl

theorem prepareDigestSelect {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (bound : x < 2^256) (ready : DigestLimbs fr a m x) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l1010ae,a,m⟩ =
        .call ⟨.l127ea0,b,n⟩ (Verify.resumeAt .l10126c 0x10126c) ∧ DigestSelect fr b n x := by
  obtain ⟨b,call,rsp,dst,src,dstLen,srcLen,flag,rbp,r13,r14,widths,preserved⟩ :=
    subtractDigest depth limit bound ready
  have wf := stagedWrites m fr.rsp x depth limit
  obtain ⟨srcWords,diffWords⟩ := stagedWords m fr.rsp x
  let n := digestStage m fr.rsp x
  have sub (k : BitVec 64) (hk : k.toNat ≤ 2208) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have base : fr.low.toNat = fr.rsp.toNat - 2208 := by rw [low,sub _ (by decide)]; rfl
  have inFrame : RegionsWithin [⟨(fr.rsp - 288).toNat,176⟩] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_⟩
    simp (disch := decide) only [Activation.region,base,sub,BitVec.reduceToNat]
    omega
  have saved (k : BitVec 64) (hk : k.toNat ≤ 112) :
      memLoad n (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply wf.memLoad_eq
    refine ⟨by rw [sub _ (by omega)]; omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change (fr.rsp - 288).toNat + 176 ≤ (fr.rsp - k).toNat
    simp (disch := first | omega | decide) only [sub,BitVec.reduceToNat]
    omega
  have back := saved 0 (by decide)
  rw [show fr.rsp - (0 : BitVec 64) = fr.rsp from BitVec.sub_zero _] at back
  have atoms := ready.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_,df,_,mx,ft,fc,s9,s2,s6,s7,s3,s12,s13,s14,s15,s5,rd,ret,retL,
    win,room,align,_,_,rd0,got0,rd1,got1,rd2,got2,rd3,got3,apart,_⟩ := atoms
  have global (k : BitVec 64) (loK : 0x203dc8 ≤ k.toNat) (hiK : k.toNat ≤ 0x203e20) :
      memLoad n k 64 = memLoad m k 64 := by
    apply wf.memLoad_eq
    refine ⟨by omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change k.toNat + 8 ≤ (fr.rsp - 288).toNat ∨ (fr.rsp - 288).toNat + 176 ≤ k.toNat
    rw [sub _ (by decide)]
    change k.toNat + 8 ≤ fr.rsp.toNat - 288 ∨ fr.rsp.toNat - 288 + 176 ≤ k.toNat
    omega
  refine ⟨b,n,call,⟨⟨?_,ready.writes.trans wf inFrame⟩,rsp,?_,dst,src,dstLen,srcLen,flag,
    rbp,r13,widths,srcWords,diffWords⟩⟩
  · simp only [Fn100ea0.frameAt,Fn100ea0.frameAtG1,Atom.All,Atom.Holds]
    refine ⟨?_,?_,?_,?_,?_,?_,(saved _ (by decide)).trans s9,(saved _ (by decide)).trans s2,
      (saved _ (by decide)).trans s6,(saved _ (by decide)).trans s7,(saved _ (by decide)).trans s3,
      (saved _ (by decide)).trans s12,(saved _ (by decide)).trans s13,(saved _ (by decide)).trans s14,
      (saved _ (by decide)).trans s15,(saved _ (by decide)).trans s5,rd.of_frame wf,back.trans ret,
      retL,win.of_frame wf,room,align,rd0.of_frame wf,(global _ (by decide) (by decide)).trans got0,
      rd1.of_frame wf,(global _ (by decide) (by decide)).trans got1,rd2.of_frame wf,
      (global _ (by decide) (by decide)).trans got2,rd3.of_frame wf,
      (global _ (by decide) (by decide)).trans got3,by omega,trivial⟩
    all_goals simp only [Fin.getElem_fin, Vector.getElem_set]
    all_goals first | rfl | exact r14 | exact (preserved _ (by decide)).trans df |
      exact (preserved _ (by decide)).trans mx | exact (preserved _ (by decide)).trans ft |
      exact (preserved _ (by decide)).trans fc
  · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Signing.Nonce.Initialize
