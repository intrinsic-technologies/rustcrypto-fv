import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {fr : Activation} {input : Input}

theorem copyBase (env : Environment fr input) : (sp fr).toNat = fr.rsp.toNat - 712 :=
  BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from by
    have := env.depth
    change 712 ≤ fr.rsp.toNat
    omega)

theorem copySlot (env : Environment fr input) : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
  BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from by
    have := env.depth
    change 8 ≤ (sp fr).toNat
    rw [copyBase env]
    omega)

theorem copyAddr (env : Environment fr input) (i : Nat) (hi : i ≤ 712) :
    (sp fr + BitVec.ofNat 64 i).toNat = (sp fr).toNat + i := by
  have := copyBase env
  have := env.limit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem padWrites (env : Environment fr input) (m : Ram) (second : Bool) (k : Nat) (hk : k ≤ 8) :
    RamWriteFrame (moved fr m) (padWords fr second m k) [⟨(sp fr).toNat + 496,64⟩] := by
  induction k with
  | zero => exact .refl _ _
  | succ k ih =>
    apply (ih (by omega)).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp fr).toNat + 496 ≤ _ ∧ _ + 8 ≤ (sp fr).toNat + 496 + 64 ∧ _ + 8 ≤ 2^64
    rw [copyAddr env _ (by omega)]
    have := copyBase env
    have := env.limit
    omega

theorem padsFrame (env : Environment fr input) (m : Ram) (second : Bool) (k : Nat) (hk : k ≤ 8) :
    RamWriteFrame m (padWords fr second m k) [⟨(sp fr).toNat + 496,168⟩] := by
  have move : RamWriteFrame m (moved fr m) [⟨(sp fr).toNat + 496,168⟩] := by
    apply Sec1.Wrapper.Copy.memCopy_frame (.refl _ _)
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp fr).toNat + 496 ≤ (sp fr + 560).toNat ∧ _ + 104 ≤ (sp fr).toNat + 496 + 168 ∧ _ + 104 ≤ 2^64
    rw [show (sp fr + 560).toNat = (sp fr).toNat + 560 from copyAddr env 560 (by decide)]
    have := copyBase env
    have := env.limit
    omega
  apply move.trans (padWrites env m second k hk)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_,List.mem_singleton_self _,Nat.le_refl _,by exact Nat.add_le_add_left (show 64 ≤ 168 by decide) _⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
