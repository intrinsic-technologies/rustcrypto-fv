import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def compressRegions (s : BitVec 64) : List MemoryRegion :=
  [⟨(s - 344).toNat, 344⟩, ⟨(s + 391).toNat, 41⟩]

theorem compressFrame {fr : Activation} {input : Input} {state : State}
    {a b : Verify.Core.Registers} {m n : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second false) fr a m state) (slots : second = true → Slots fr m)
    (writes : RamWriteFrame m n (compressRegions (sp fr))) (rsp : b[4] = ⟨64,sp fr⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,14,15,22,39,50,51] → b[i] = a[i])
    (r13 : b[13] = if second then ⟨64,sp fr + 392⟩ else a[13]) :
    Live (head second true) fr b n state ∧ (second = true → Slots fr n) := by
  have depth := env.depth
  have limit := env.limit
  have base := Absorb.spNat env
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have leftStart : (sp fr - 344).toNat = (sp fr).toNat - 344 :=
    BitVec.toNat_sub_of_le
      (show (344 : BitVec 64) ≤ sp fr from (by change 344 ≤ (sp fr).toNat; omega))
  have rightStart : (sp fr + 391).toNat = (sp fr).toNat + 391 :=
    Absorb.spAddNat env 391 (by decide)
  have localWrites : Absorb.LocalWrites fr (compressRegions (sp fr)) := by
    intro r hr
    simp only [compressRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat ≤ (sp fr - 344).toNat ∧ (sp fr - 344).toNat + 344 ≤ _
      omega
    · change fr.low.toNat ≤ (sp fr + 391).toNat ∧ (sp fr + 391).toNat + 41 ≤ _
      omega
  have outside (off : Nat) (h : off + 8 ≤ 391) :
      Outside (compressRegions (sp fr)) (sp fr + BitVec.ofNat 64 off) 8 := by
    have addr := Absorb.spAddNat env off (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [compressRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (sp fr - 344).toNat + 344 ≤ _
      omega
    · left
      change _ ≤ (sp fr + 391).toNat
      omega
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      b[i].width = 64 := by
    by_cases h : i.val = 13
    · obtain rfl : i = 13 := Fin.ext h
      change b[13].width = 64
      rw [r13]
      cases second
      · exact live.savedWidths 13 (by decide)
      · rfl
    · rw [keep i (by
        simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil,
          or_false] at hi ⊢
        omega)]
      exact live.savedWidths i hi
  have tail (old : Absorb.FrameTail fr a m) : Absorb.FrameTail fr b n :=
    Absorb.frameTailAfter env old writes localWrites
  refine ⟨Absorb.liveAfter env live writes localWrites ?_ widths ?_, fun h => ?_⟩
  · cases second
    · obtain ⟨_, df, bx, bp, _, _, _, r12, old13, r14, r15, mx, ft, fc, rest⟩ := live.atoms
      exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 3 (by decide)).trans bx,
        (keep 5 (by decide)).trans bp, (keep 12 (by decide)).trans r12, r13.trans old13,
        (keep 14 (by decide)).trans r14, (keep 15 (by decide)).trans r15,
        (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
        (keep 51 (by decide)).trans fc, tail rest⟩
    · obtain ⟨_, df, bx, r14, mx, ft, fc, rest⟩ := live.atoms
      exact ⟨rsp, (keep 22 (by decide)).trans df, (keep 3 (by decide)).trans bx,
        (keep 14 (by decide)).trans r14, (keep 39 (by decide)).trans mx,
        (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc, tail rest⟩
  · cases second <;> intro impossible <;> cases impossible
  · exact Absorb.slotsAfter (slots h) writes (outside 8 (by decide)) (outside 112 (by decide))
      (outside 120 (by decide))

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
