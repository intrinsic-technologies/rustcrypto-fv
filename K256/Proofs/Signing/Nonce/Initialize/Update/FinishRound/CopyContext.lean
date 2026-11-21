import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.CopyContext.Frame
import K256.Proofs.Verify.LIR.Fn103f30
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Signing.UpdateV.Copy
import K256.Proofs.Signing.UpdateV.Finalize.Memory
import K256.Proofs.Verify.Hash.Update.Copy
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private def copyReturn (second : Bool) (input : Input) : BitVec 64 :=
  if second then 0x1048d8 else if seeded input then 0x10432a else 0x1046c0

set_option maxRecDepth 3200 in
set_option maxHeartbeats 1000000 in
private theorem enterContextCopy {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool)
    (live : Live (digestAt second input) fr a m state)
    (w : Writable Extracted.programImage m (sp fr - 8) 8) :
    ∃ ca : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨digestAt second input, a, m⟩ =
        .call ⟨.l12a820, ca, memStore m (sp fr - 8) (copyReturn second input)⟩
          (Verify.Hash.Update.returnFrame (finalizeAt second input) (copyReturn second input)) ∧
      ca[7].get 64 = sp fr + 496 ∧ ca[6].get 64 = context fr second ∧
      ca[2].get 64 = 168 ∧ ca[4].get 64 = sp fr - 8 ∧ ca[22].get 1 = 0 ∧
      ca[3] = ⟨64, sp fr + 496⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → ca[i] = a[i]) := by
  have entry := live.atoms
  cases second
  case' false => cases input
  all_goals
    simp only [digestAt, seeded, Bool.false_eq_true, ite_false, ite_true, Fn103f30.frameAt,
      Fn103f30.frameAtG5, Atom.All, Atom.Holds] at entry
    obtain ⟨spEq, df, rest⟩ := entry
    have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) spEq
    have direction : a[22].get 1 = 0 := congrArg (Value.get 1) df
    obtain ⟨read, target⟩ : Readable m 0x203dd0 8 ∧ memLoad m 0x203dd0 64 = 0x12a820 := by
      repeat' first | exact ⟨rest.1, rest.2.1⟩ | obtain ⟨_, rest⟩ := rest
    have got : LoadOk m 0x203dd0 8 := ⟨read.low, read.present⟩
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · first
      | change program.runBlock _ ⟨.l1046a2, _, _⟩ = _
        have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x1046ba 6 :=
          ParseSignature.storeOk_of_codeRange (off := 24) w
            (fun x hx => Common.fnCode_subset_programImage x (code_l1046a2 x hx)) (by decide +kernel)
      | change program.runBlock _ ⟨.l10430c, _, _⟩ = _
        have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x104324 6 :=
          ParseSignature.storeOk_of_codeRange (off := 24) w
            (fun x hx => Common.fnCode_subset_programImage x (code_l10430c x hx)) (by decide +kernel)
      | change program.runBlock _ ⟨.l1048ba, _, _⟩ = _
        have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x1048d2 6 :=
          ParseSignature.storeOk_of_codeRange (off := 24) w
            (fun x hx => Common.fnCode_subset_programImage x (code_l1048ba x hx)) (by decide +kernel)
      cfg_eval [rsp, got, target, push] <;> rfl
    · refine ⟨rfl, rfl, rfl, rfl, direction, rfl, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem copyRoundContext {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (digestAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key (message second input state)) :
    ∃ b n, Verify.Core.Reaches (digestAt second input) a m (finalizeAt second input) b n ∧
      Live (finalizeAt second input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      b[3] = ⟨64, sp fr + 496⟩ ∧
      UpdateV.HmacStateAt n (sp fr + 496) state.key (message second input state) := by
  have depth := env.depth
  have limit := env.limit
  have sn : (sp fr).toNat = fr.rsp.toNat - 712 :=
    BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from (by change 712 ≤ fr.rsp.toNat; omega))
  let slot := sp fr - 8
  let dst := sp fr + 496
  let src := context fr second
  let ret := copyReturn second input
  let pushed := memStore m slot ret
  have sl : slot.toNat = (sp fr).toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have dl : dst.toNat = (sp fr).toNat + 496 := Nat.mod_eq_of_lt (by change (sp fr).toNat + 496 < 2^64; omega)
  have soff : src.toNat = (sp fr).toNat + (if second then 328 else 160) := by
    cases second
    · exact Nat.mod_eq_of_lt (by change (sp fr).toNat + 160 < 2^64; omega)
    · exact Nat.mod_eq_of_lt (by change (sp fr).toNat + 328 < 2^64; omega)
  have stk := env.stack.of_frame live.writes
  have lo : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)
  have ws : Writable Extracted.programImage m slot 8 := stk.sub (by omega) (by omega)
  obtain ⟨ca, call, di, si, size, rsp, df, bx, keep⟩ := enterContextCopy second live ws
  let pushedRegions : List MemoryRegion := [⟨slot.toNat, 8⟩]
  have pf : RamWriteFrame m pushed pushedRegions := (RamWriteFrame.refl _ _).memStore ret
    ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by change slot.toNat + 8 ≤ 2^64; omega⟩
  have srcBounds : (sp fr).toNat ≤ src.toNat ∧ src.toNat + 168 ≤ dst.toNat := by
    split at soff <;> omega
  have sc := UpdateV.Finalize.hmacAfter pf (p := src) (by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (show slot.toNat + 8 ≤ src.toNat by omega)) ctx
  have pushedStack := stk.of_frame pf
  have read : Readable pushed src 168 := pushedStack.readable.sub (by omega) (by omega)
  have write : Writable Extracted.programImage pushed dst 168 := pushedStack.sub (by omega) (by omega)
  have retEq : memLoad pushed slot 64 = ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retLow : ret.toNat < 2^32 := by
    change (copyReturn second input).toNat < 2^32
    unfold copyReturn
    split
    · decide
    · split <;> decide
  obtain ⟨out, run, copied, returned, _, back, kept⟩ :=
    Verify.Hash.Update.memcpy di si size rsp df read write (Or.inl srcBounds.2)
      (by apply RangeApart.of_offsets rfl (addr_sub _ _); decide)
      (ws.readable.of_frame pf) (retEq ▸ retLow)
  have stackBack : out.values[4] = ⟨64, sp fr⟩ := by
    rw [back, BitVec.sub_add_cancel]
  have ptr := (kept 3 (by decide)).trans bx
  have wf : RamWriteFrame m out.store (contextCopyRegions fr) := by
    rw [copied]
    apply Sec1.Wrapper.Copy.memCopy_frame
    · apply (RamWriteFrame.refl _ _).memStore
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by change slot.toNat + 8 ≤ 2^64; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _,
          by change dst.toNat + 168 ≤ 2^64; omega⟩
  obtain ⟨next, saved⟩ := contextCopyFrame second env live slots wf stackBack ptr (fun i hi =>
    (kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans (keep i hi))
  refine ⟨out.values, out.store, ?_, next, saved, ptr, ?_⟩
  · have resumed := ParseSignature.exec_reaches_resume run
        (Verify.Hash.Update.returnFrame (finalizeAt second input) ret) [] (by
          rw [returned, retEq]
          cases second <;> cases input <;> rfl)
    exact .step (congrArg (Transfer.next _ []) call) resumed
  · rw [copied]
    exact sc.memCopy

end K256.Proofs.Signing.Nonce.Initialize.Update
