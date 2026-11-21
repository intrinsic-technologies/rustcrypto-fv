import AesGcm.Proofs.AES16.Encrypt.State
import AesGcm.Proofs.Machine.Runtime.Guards

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def callPointer (use256 : Bool) (fr : Activation) : BitVec 64 :=
  fr.rsp - BitVec.ofNat 64 (if use256 then 128 else 112)

def callRegion (use256 : Bool) (fr : Activation) : MemoryRegion :=
  ⟨fr.low.toNat, (callPointer use256 fr).toNat - fr.low.toNat⟩

theorem window_eq (use256 : Bool) :
    (frameInfo use256).window = (if use256 then 368 else 352) := by
  cases use256 <;> rfl

theorem call_geometry (use256 : Bool) (code : CodeMap) (mem : Ram) (fr : Activation)
    (n : Nat) (hn : n ≤ 240)
    (hstack : Writable code mem
      (fr.rsp - BitVec.ofNat 64 (frameInfo use256).window) (frameInfo use256).window)
    (hroom : fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat)
    (halign : fr.rsp.toNat % 16 = 8) :
    fr.rsp.toNat ≤ 2 ^ 32 ∧
    (callPointer use256 fr).toNat = fr.rsp.toNat - (if use256 then 128 else 112) ∧
    (buffer use256 fr).toNat = fr.rsp.toNat - (if use256 then 112 else 104) ∧
    Readable mem (callPointer use256 fr) 8 ∧
    Writable code mem (callPointer use256 fr - BitVec.ofNat 64 n) n ∧
    fr.low.toNat + n ≤ (callPointer use256 fr).toNat ∧
    (callPointer use256 fr).toNat % 16 = 8 ∧
    (⟨fr.low.toNat, (callPointer use256 fr).toNat + 8 - fr.low.toNat⟩ : MemoryRegion).Disjoint
      (span (buffer use256 fr) 16) ∧
    RegionsWithin [callRegion use256 fr, span (buffer use256 fr) 16,
      span (callPointer use256 fr) 8] [fr.region] ∧
    ∀ k : Nat, k ≤ 72 → Outside
      [callRegion use256 fr, span (buffer use256 fr) 16, span (callPointer use256 fr) 8]
      (fr.rsp - BitVec.ofNat 64 k) 8 := by
  let w := (frameInfo use256).window
  let d : Nat := if use256 then 128 else 112
  let b : Nat := if use256 then 112 else 104
  have hparams : w = d + 240 ∧ 112 ≤ d ∧ d ≤ 128 ∧ 104 ≤ b ∧ b ≤ 112 ∧
      b + 8 ≤ d ∧ d % 16 = 0 := by
    cases use256 <;> decide
  have hroot : w ≤ fr.rsp.toNat := by omega
  have hsub (k : Nat) (hk : k ≤ w) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hk64 : k < 2 ^ 64 := by omega
    have hksp : BitVec.ofNat 64 k ≤ fr.rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
      omega
    rw [BitVec.toNat_sub_of_le hksp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hrootNat := hsub w (Nat.le_refl _)
  have hlow := hstack.readable.low
  change (fr.rsp - BitVec.ofNat 64 w).toNat + w ≤ 2 ^ 32 at hlow
  rw [hrootNat] at hlow
  have hsp : fr.rsp.toNat ≤ 2 ^ 32 := by omega
  have hcp : (callPointer use256 fr).toNat = fr.rsp.toNat - d := hsub d (by omega)
  have hbuf : (buffer use256 fr).toNat = fr.rsp.toNat - b := by
    cases use256 <;> exact hsub _ (by dsimp only [b, d, w, frameInfo] at *; omega)
  have hchildAddr : callPointer use256 fr - BitVec.ofNat 64 n =
      fr.rsp - BitVec.ofNat 64 (d + n) := by
    change fr.rsp - BitVec.ofNat 64 d - BitVec.ofNat 64 n = _
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hchildNat : (callPointer use256 fr - BitVec.ofNat 64 n).toNat =
      fr.rsp.toNat - (d + n) := by
    rw [hchildAddr]
    exact hsub _ (by omega)
  refine ⟨hsp, hcp, hbuf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hstack.readable.sub
    · rw [hcp, hrootNat]
      omega
    · rw [hcp, hrootNat]
      omega
  · apply hstack.sub
    · rw [hchildNat, hrootNat]
      omega
    · rw [hchildNat, hrootNat]
      omega
  · rw [hcp]
    omega
  · rw [hcp]
    omega
  · intro x hx hxb
    change fr.low.toNat ≤ x ∧ x < fr.low.toNat +
      ((callPointer use256 fr).toNat + 8 - fr.low.toNat) at hx
    change (buffer use256 fr).toNat ≤ x ∧ x < (buffer use256 fr).toNat + 16 at hxb
    rw [hcp] at hx
    rw [hbuf] at hxb
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals refine ⟨fr.region, by simp only [List.mem_singleton], ?_, ?_⟩
    all_goals simp only [callRegion, span, Activation.region, hcp, hbuf]
    all_goals omega
  · intro k hk
    have hslot := hsub k (by omega)
    refine ⟨?_, ?_⟩
    · rw [hslot]
      omega
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals right
      all_goals simp only [callRegion, span, hcp, hbuf, hslot]
      all_goals omega

theorem output_slot_outside {fr : Activation}
    (hroom : fr.low.toNat + 72 ≤ fr.rsp.toNat) (hsp : fr.rsp.toNat ≤ 2 ^ 32)
    (hsep : (callStack fr).Disjoint (span fr.rdi 16)) (k : Nat) (hk : k ≤ 72) :
    Outside [span fr.rdi 16] (fr.rsp - BitVec.ofNat 64 k) 8 := by
  have hslot : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hk64 : k < 2 ^ 64 := by omega
    have hks : BitVec.ofNat 64 k ≤ fr.rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
      omega
    rw [BitVec.toNat_sub_of_le hks, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hb := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 16 (by omega) (by decide) hsep
  refine ⟨?_, ?_⟩
  · rw [hslot]
    omega
  · intro r hr
    have he : r = span fr.rdi 16 := List.mem_singleton.mp hr
    subst r
    simp only [span, hslot]
    omega


def preciseActivation (use256 : Bool) (fr : Activation) : Activation :=
  {fr with low := fr.rsp - BitVec.ofNat 64 (frameInfo use256).window}

theorem precise_room (use256 : Bool) (fr : Activation)
    (hroom : fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat) :
    (preciseActivation use256 fr).low.toNat + (frameInfo use256).window = fr.rsp.toNat := by
  have hw : (frameInfo use256).window < 2 ^ 64 := by rw [window_eq]; cases use256 <;> decide
  have hsub : BitVec.ofNat 64 (frameInfo use256).window ≤ fr.rsp := by
    change (BitVec.ofNat 64 (frameInfo use256).window).toNat ≤ fr.rsp.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
    omega
  simp only [preciseActivation, BitVec.toNat_sub_of_le hsub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  omega

theorem precise_within (use256 : Bool) (fr : Activation)
    (hroom : fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat) :
    RegionsWithin [(preciseActivation use256 fr).region] [fr.region] := by
  have hp := precise_room use256 fr hroom
  intro r hr
  have he : r = (preciseActivation use256 fr).region := List.mem_singleton.mp hr
  subst r
  refine ⟨fr.region, by simp only [List.mem_singleton], ?_, ?_⟩
  all_goals simp only [Activation.region, preciseActivation] at *
  all_goals omega

theorem call_slot_outside (use256 : Bool) (code : CodeMap) (mem : Ram) (fr : Activation)
    (hstack : Writable code mem
      (fr.rsp - BitVec.ofNat 64 (frameInfo use256).window) (frameInfo use256).window)
    (hroom : fr.low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat)
    (halign : fr.rsp.toNat % 16 = 8)
    (hsep : 0x201238 + (frameInfo use256).window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)
    (a : BitVec 64) (hlo : 0x201210 ≤ a.toNat) (hhi : a.toNat + 8 ≤ 0x201238) :
    Outside [callRegion use256 (preciseActivation use256 fr), span (buffer use256 fr) 16,
      span (callPointer use256 fr) 8] a 8 := by
  have hp := precise_room use256 fr hroom
  have hpr : (preciseActivation use256 fr).low.toNat + (frameInfo use256).window ≤
      (preciseActivation use256 fr).rsp.toNat := by
    change (preciseActivation use256 fr).low.toNat + (frameInfo use256).window ≤ fr.rsp.toNat
    omega
  obtain ⟨_, _, _, _, _, _, _, _, hwithin, _⟩ :=
    call_geometry use256 code mem (preciseActivation use256 fr) 0 (by decide) hstack hpr halign
  refine ⟨by omega, ?_⟩
  intro r hr
  obtain ⟨r', hr', hstart, hend⟩ := hwithin r hr
  have he : r' = (preciseActivation use256 fr).region := List.mem_singleton.mp hr'
  subst r'
  simp only [Activation.region] at hstart hend
  change r.start + r.size ≤ (preciseActivation use256 fr).low.toNat +
    (fr.rsp.toNat - (preciseActivation use256 fr).low.toNat) at hend
  omega

end AesGcm.Proofs.Machine.AES16.Encrypt
