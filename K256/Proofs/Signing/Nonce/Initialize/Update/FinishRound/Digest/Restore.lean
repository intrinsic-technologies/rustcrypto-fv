import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.Digest.Call

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2


theorem digestRestore {fr : Activation} {input : Input} {state : State}
    {a b : Verify.Core.Registers} {m t n : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (finalizeAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (push : RamWriteFrame m t (digestWrites fr second))
    (writes : RamWriteFrame t n [UpdateV.Finalize.scratch (sp fr - 8),⟨(digestPtr fr second).toNat,32⟩])
    (rsp : b[4] = ⟨64,sp fr⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) :
    Live (keyAt second input) fr b n state ∧ (seeded input = true → Slots fr n) := by
  let rs : List MemoryRegion := [⟨(sp fr).toNat - 712,712⟩,⟨(digestPtr fr second).toNat,32⟩]
  have dep := env.depth
  have lim := env.limit
  have base : (sp fr).toNat = fr.rsp.toNat - 712 :=
    BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from by change 712 ≤ fr.rsp.toNat; omega)
  have sub : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from by change 8 ≤ (sp fr).toNat; omega)
  have bot : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have add (k : BitVec 64) (h : k.toNat ≤ 160) : (sp fr + k).toNat = (sp fr).toNat + k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have dst : (digestPtr fr second).toNat = (sp fr).toNat + (if second then 128 else 16) := by
    cases second <;> exact add _ (by decide)
  have frame : RamWriteFrame m n rs := by
    refine ((RamWriteFrame.refl m rs).trans push ?_).trans writes ?_
    all_goals
      intro r hr
      rcases List.mem_cons.mp hr with rfl | h
      · refine ⟨⟨(sp fr).toNat - 712,712⟩,List.mem_cons_self,?_,?_⟩
        all_goals dsimp only [UpdateV.Finalize.scratch]; rw [sub]; omega
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _⟩
  have loc : Absorb.LocalWrites fr rs := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · change fr.low.toNat ≤ (sp fr).toNat - 712 ∧ (sp fr).toNat - 712 + 712 ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      change fr.low.toNat ≤ (digestPtr fr second).toNat ∧ (digestPtr fr second).toNat + 32 ≤ _
      rw [dst]; split <;> omega
  have outside (k : BitVec 64) (h : k.toNat ≤ 120)
      (disj : k.toNat + 8 ≤ (if second then 128 else 16) ∨ (if second then 128 else 16) + 32 ≤ k.toNat) :
      Outside rs (sp fr + k) 8 := by
    constructor
    · rw [add _ (by omega)]; change _ + 8 ≤ 2^64; omega
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | h'
      · right
        change (sp fr).toNat - 712 + 712 ≤ (sp fr + k).toNat
        rw [add _ (by omega)]; omega
      · obtain rfl := List.mem_singleton.mp h'
        change (sp fr + k).toNat + 8 ≤ (digestPtr fr second).toNat ∨
          (digestPtr fr second).toNat + 32 ≤ (sp fr + k).toNat
        rw [add _ (by omega), dst]; omega
  have slotState := frame.memLoad_eq (k := 64) (outside 120 (by decide) (by cases second <;> decide))
  have save : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64 := by
    intro i hi
    rw [keep i (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact live.savedWidths i hi
  refine ⟨Absorb.liveAfter env live frame loc ?_ save (by cases second <;> cases input <;> intro h <;> cases h), ?_⟩
  · have old := live.atoms
    have st : fr.rsp - 592 = sp fr + 120 := by unfold sp; bv_omega
    cases second with
    | false =>
      cases input with
      | empty =>
        obtain ⟨_,df,bp,r14,r15,mx,ft,fc,tail⟩ := old
        exact ⟨rsp,(keep 22 (by decide)).trans df,(keep 5 (by decide)).trans bp,
          (keep 14 (by decide)).trans r14,(keep 15 (by decide)).trans r15,(keep 39 (by decide)).trans mx,
          (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
          Absorb.frameTailAfter env (a := a) tail frame loc⟩
      | seeded _ _ =>
        obtain ⟨_,df,r14,mx,ft,fc,slot,tail⟩ := old
        rw [← st] at slotState
        exact ⟨rsp,(keep 22 (by decide)).trans df,(keep 14 (by decide)).trans r14,(keep 39 (by decide)).trans mx,
          (keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,slotState.trans slot,
          Absorb.frameTailAfter env (a := a) tail frame loc⟩
    | true =>
      obtain ⟨_,df,mx,ft,fc,tail⟩ := old
      exact ⟨rsp,(keep 22 (by decide)).trans df,(keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,
        (keep 51 (by decide)).trans fc,Absorb.frameTailAfter env (a := a) tail frame loc⟩
  · intro hs
    apply Absorb.slotsAfter (slots hs) frame
    all_goals apply outside _ (by decide) (by cases second <;> decide)

end K256.Proofs.Signing.Nonce.Initialize.Update
