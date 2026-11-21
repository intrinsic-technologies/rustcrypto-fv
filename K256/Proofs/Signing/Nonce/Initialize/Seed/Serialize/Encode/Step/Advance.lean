import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize.Encode
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Verify.Core
open Generate.Generator.Multiply (scalarWords)

theorem advance {a r : Registers} {fr : Activation} {m : Ram} {k x : Nat} (hk : k < 4)
    (atoms : Atom.All Extracted.programImage a m (Fn100000.frameAt .l100110 fr))
    (saved : ∀ i : Fin Reg.count, i.val ∈ [13,14,22,39,50,51] → r[i] = a[i])
    (sp : r[4] = ⟨64,fr.rsp - 72⟩)
    (cursor : r[3] = ⟨64,BitVec.ofNat 64 (32-8*(k+1))⟩)
    (index : r[5] = ⟨64,BitVec.ofNat 64 (k+1)⟩)
    (zero : r[12] = ⟨64,0⟩) (count : r[15] = ⟨64,4⟩)
    (widths : ParseSignature.ArgumentWidths r)
    (writes : RamWriteFrame fr.original m [fr.region, ⟨fr.rdx.toNat,32⟩])
    (words : ∀ i (_hi : i < k+1) (bound : i < 4),
      memLoad m (wordAddr fr.rdx 64 (3-i)) 64 = bswapSpec ((scalarWords x)[i])) :
    ∃ b, Reaches .l10014b r m (label (k+1)) b m ∧ Loop fr x (k+1) b m := by
  have cf : (!(cmpSpec (4 : BitVec 64) (BitVec.ofNat 64 (k+1))).ZF) = decide (k+1<4) := by
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel
  have ri := congrArg (Value.get 64) index
  have rc := congrArg (Value.get 64) count
  have rb := congrArg (Value.get 64) cursor
  change r[5].get 64 = BitVec.ofNat 64 (k+1) at ri
  change r[15].get 64 = 4 at rc
  change r[3].get 64 = BitVec.ofNat 64 (32-8*(k+1)) at rb
  obtain ⟨b, jump, re, kept⟩ : ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l10014b,r,m⟩ =
        .jump ⟨label (k+1),b,m⟩ ∧ b[2] = ⟨64,BitVec.ofNat 64 (32-8*(k+1))⟩ ∧
        ∀ i : Fin Reg.count, i.val ∈ [1,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] → b[i] = r[i] := by
    by_cases more : k+1<4
    all_goals
      rw [show label (k+1) = _ from (by first | exact ite_eq_left more | exact ite_eq_right more)]
      refine ⟨?_, ?run, ?post⟩
      case run =>
        cfg_eval [rc,ri,rb]
        simp only [cf,decide_eq_true_eq,more,↓reduceIte]
        rfl
      case post =>
        refine ⟨rfl,?_⟩
        rintro ⟨i,_⟩ hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨b,.single ?_,?_,re,(kept 3 (by decide)).trans cursor,
    (kept 5 (by decide)).trans index,(kept 12 (by decide)).trans zero,(kept 15 (by decide)).trans count,
    ?_,writes,words⟩
  · change (program.runBlock _ _).next _ [] = _
    rw [jump]
    rfl
  · simp only [Fn100000.frameAt,Fn100000.frameAtG0, Atom.All, Atom.Holds] at atoms
    obtain ⟨_,df,p,q,mx,ft,fc,stack⟩ := atoms
    have rr (i : Fin Reg.count) (hs : i.val ∈ [13,14,22,39,50,51]) : b[i] = a[i] := by
      apply Eq.trans (kept i ?_) (saved i hs)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ⊢
      omega
    have sp' := (kept 4 (by decide)).trans sp
    by_cases more : k+1<4
    · rw [label,ite_eq_left more]
      exact ⟨sp',(rr 22 (by decide)).trans df,(rr 13 (by decide)).trans p,(rr 14 (by decide)).trans q,
        (rr 39 (by decide)).trans mx,(rr 50 (by decide)).trans ft,(rr 51 (by decide)).trans fc,stack⟩
    · rw [label,ite_eq_right more]
      obtain ⟨bx,r12,r13,r14,r15,bp,retR,ret,retL,area,base,align,_⟩ := stack
      exact ⟨sp',(rr 22 (by decide)).trans df,(rr 39 (by decide)).trans mx,(rr 50 (by decide)).trans ft,
        (rr 51 (by decide)).trans fc,bx,r12,r13,r14,r15,bp,retR,ret,retL,area,base,align,trivial⟩
  · rintro ⟨i,hi⟩ h
    have w := widths ⟨i,hi⟩ h
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (congrArg Value.width (kept 7 (by decide))).trans w
    · exact (congrArg Value.width (kept 6 (by decide))).trans w
    · exact congrArg Value.width re
    · exact (congrArg Value.width (kept 1 (by decide))).trans w
    · exact (congrArg Value.width (kept 8 (by decide))).trans w
    · exact (congrArg Value.width (kept 9 (by decide))).trans w
end K256.Proofs.Signing.Nonce.Initialize.Encode
