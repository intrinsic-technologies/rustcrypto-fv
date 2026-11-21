import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Bounds

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

theorem copyLive {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second true) fr a m state) (slots : second = true → Slots fr m)
    {b : Verify.Core.Registers} (rsp : b[4] = ⟨64, sp fr⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) :
    Live (appendAt second) fr b (copied fr second m) state ∧
      (second = true → Slots fr (copied fr second m)) := by
  let regs : List MemoryRegion := [⟨(sp fr - 8).toNat, 8⟩, ⟨(sp fr).toNat + 160, 504⟩]
  have depth := env.depth
  have limit := env.limit
  have base := copyBase env
  have slot := copySlot env
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have inside : Absorb.LocalWrites fr regs := by
    intro r hr
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  have writes : RamWriteFrame m (copied fr second m) regs := by
    apply Sec1.Wrapper.Copy.memCopy_frame
    · apply RamWriteFrame.memStore
      · apply (RamWriteFrame.refl m regs).trans (padsFrame env m second 8 (by decide))
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
        change (sp fr).toNat + 160 ≤ (sp fr).toNat + 496 ∧ (sp fr).toNat + 496 + 168 ≤ (sp fr).toNat + 160 + 504
        omega
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by change (sp fr - 8).toNat + 8 ≤ 2^64; omega⟩
    · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      change (sp fr).toNat + 160 ≤ (context fr second).toNat ∧ _ + 168 ≤ (sp fr).toNat + 160 + 504 ∧ _ + 168 ≤ 2^64
      cases second
      · simp only [context, Bool.false_eq_true, ite_false]
        have h : (sp fr + 160).toNat = (sp fr).toNat + 160 := copyAddr env 160 (by decide)
        omega
      · simp only [context, ite_true]
        have h : (sp fr + 328).toNat = (sp fr).toNat + 328 := copyAddr env 328 (by decide)
        omega
  have outside (i : Nat) (hi : i ≤ 152) : Outside regs (sp fr + BitVec.ofNat 64 i) 8 := by
    have pos := copyAddr env i (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (show (sp fr - 8).toNat + 8 ≤ _ by omega)
    · exact Or.inl (show _ ≤ (sp fr).toNat + 160 by omega)
  refine ⟨Absorb.liveAfter env live writes inside ?_ ?_ ?_, fun h =>
    Absorb.slotsAfter (slots h) writes (outside 8 (by decide)) (outside 112 (by decide))
      (outside 120 (by decide))⟩
  · cases second
    · obtain ⟨_, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, rest⟩ := live.atoms
      exact ⟨rsp, (kept 22 (by decide)).trans df, (kept 3 (by decide)).trans bx,
        (kept 5 (by decide)).trans bp, (kept 12 (by decide)).trans r12,
        (kept 13 (by decide)).trans r13, (kept 14 (by decide)).trans r14,
        (kept 15 (by decide)).trans r15, (kept 39 (by decide)).trans mx,
        (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
        Absorb.frameTailAfter env (a := a) (b := b) rest writes inside⟩
    · obtain ⟨_, df, bx, r14, mx, ft, fc, rest⟩ := live.atoms
      exact ⟨rsp, (kept 22 (by decide)).trans df, (kept 3 (by decide)).trans bx,
        (kept 14 (by decide)).trans r14, (kept 39 (by decide)).trans mx,
        (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
        Absorb.frameTailAfter env (a := a) (b := b) rest writes inside⟩
  · intro i hi
    rw [kept i (by simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact live.savedWidths i hi
  · cases second <;> intro h <;> cases h

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
