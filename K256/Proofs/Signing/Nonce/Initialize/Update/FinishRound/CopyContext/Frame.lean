import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def contextCopyRegions (fr : Activation) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat, 8⟩, ⟨(sp fr + 496).toNat, 168⟩]

theorem contextCopyFrame {fr : Activation} {input : Input} {state : State}
    {a b : Verify.Core.Registers} {m n : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (digestAt second input) fr a m state)
    (slots : seeded input = true → Slots fr m)
    (writes : RamWriteFrame m n (contextCopyRegions fr))
    (rsp : b[4] = ⟨64, sp fr⟩) (rbx : b[3] = ⟨64, sp fr + 496⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i]) :
    Live (finalizeAt second input) fr b n state ∧ (seeded input = true → Slots fr n) := by
  have depth := env.depth
  have limit := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have base : (sp fr).toNat = fr.rsp.toNat - 712 :=
    BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from (by change 712 ≤ fr.rsp.toNat; omega))
  have push : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have addr (off : BitVec 64) (h : off.toNat ≤ 496) :
      (sp fr + off).toNat = (sp fr).toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have dest : (sp fr + 496).toNat = (sp fr).toNat + 496 := addr 496 (by decide)
  have localWrites : Absorb.LocalWrites fr (contextCopyRegions fr) := by
    intro r hr
    simp only [contextCopyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat ≤ (sp fr - 8).toNat ∧ (sp fr - 8).toNat + 8 ≤ _
      omega
    · change fr.low.toNat ≤ (sp fr + 496).toNat ∧ (sp fr + 496).toNat + 168 ≤ _
      omega
  have outside (off : BitVec 64) (h : off.toNat ≤ 488) :
      Outside (contextCopyRegions fr) (sp fr + off) 8 := by
    have position := addr off (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [contextCopyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (sp fr - 8).toNat + 8 ≤ _
      omega
    · left
      change _ ≤ (sp fr + 496).toNat
      omega
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      b[i].width = 64 := by
    by_cases bx : i.val = 3
    · have eq : i = 3 := Fin.ext bx
      rw [eq]
      exact congrArg Value.width rbx
    · rw [keep i (by
        simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil,
          or_false] at hi ⊢
        omega)]
      exact live.savedWidths i hi
  have tail (old : Absorb.FrameTail fr a m) : Absorb.FrameTail fr b n :=
    Absorb.frameTailAfter env old writes localWrites
  have savedSlots (h : seeded input = true) : Slots fr n :=
    Absorb.slotsAfter (slots h) writes (outside 8 (by decide)) (outside 112 (by decide))
      (outside 120 (by decide))
  refine ⟨Absorb.liveAfter env live writes localWrites ?_ widths ?_, savedSlots⟩
  · cases second
    · cases input
      · obtain ⟨_, df, bp, si, dx, mx, ft, fc, rest⟩ := live.atoms
        exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 5 (by decide)).trans bp,
          (keep 14 (by decide)).trans si, (keep 15 (by decide)).trans dx,
          (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
          (keep 51 (by decide)).trans fc, tail rest⟩
      · obtain ⟨_, df, si, mx, ft, fc, _, rest⟩ := live.atoms
        have saved : memLoad n (fr.rsp - 0x250) 64 = fr.rdi := by
          rw [show fr.rsp - 0x250 = sp fr + 120 by bv_omega]
          exact (savedSlots rfl).state
        exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 14 (by decide)).trans si,
          (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
          (keep 51 (by decide)).trans fc, saved, tail rest⟩
    · obtain ⟨_, df, mx, ft, fc, rest⟩ := live.atoms
      exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 39 (by decide)).trans mx,
        (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc, tail rest⟩
  · cases second <;> cases input <;> intro impossible <;> cases impossible

end K256.Proofs.Signing.Nonce.Initialize.Update
