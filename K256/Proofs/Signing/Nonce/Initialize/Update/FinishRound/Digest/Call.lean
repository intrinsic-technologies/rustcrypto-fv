import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Memory
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

def digestReturn (second : Bool) (input : Input) : BitVec 64 :=
  if second then 0x104918 else if seeded input then 0x10435b else 0x1046f1

def digestWrites (fr : Activation) (second : Bool) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat,8⟩, ⟨(digestPtr fr second).toNat,32⟩]

set_option maxRecDepth 3200 in
set_option maxHeartbeats 1000000 in
theorem digestCall {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (finalizeAt second input) fr a m state)
    (ptr : a[3] = ⟨64, sp fr + 496⟩) :
    ∃ b t, program.runBlock (dialect Extracted.programImage) ⟨finalizeAt second input,a,m⟩ =
        .call ⟨.l107a50,b,t⟩ ⟨keyAt second input,#v[],rfl,some ⟨64,digestReturn second input⟩⟩ ∧
      UpdateV.Finalize.Call b t (sp fr - 8) (sp fr + 496) (digestPtr fr second) ∧
      memLoad t (sp fr - 8) 64 = digestReturn second input ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (digestWrites fr second) := by
  have depth := env.depth
  have limit := env.limit
  have base : (sp fr).toNat = fr.rsp.toNat - 712 :=
    BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from by change 712 ≤ fr.rsp.toNat; omega)
  have bottom : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)
  have slot : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from by change 8 ≤ (sp fr).toNat; omega)
  have scratch : (sp fr - 8 - 704).toNat = (sp fr - 8).toNat - 704 :=
    BitVec.toNat_sub_of_le
      (show (704 : BitVec 64) ≤ sp fr - 8 from by change 704 ≤ (sp fr - 8).toNat; omega)
  have add (off : BitVec 64) (fit : off.toNat ≤ 496) :
      (sp fr + off).toNat = (sp fr).toNat + off.toNat :=
    Nat.mod_eq_of_lt (by change (sp fr).toNat + off.toNat < 2^64; omega)
  have src : (sp fr + 496).toNat = (sp fr).toNat + 496 := add _ (by decide)
  have dst : (digestPtr fr second).toNat = (sp fr).toNat + (if second then 128 else 16) := by
    cases second <;> exact add _ (by decide)
  have dstBounds : 16 ≤ (if second then 128 else 16 : Nat) ∧
      (if second then 128 else 16 : Nat) ≤ 128 := by cases second <;> decide
  have stack := env.stack.of_frame live.writes
  have push : InRegions (digestWrites fr second) (sp fr - 8) 8 :=
    ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by change (sp fr - 8).toNat + 8 ≤ 2^64; omega⟩
  have word (off : BitVec 64) (lo : (if second then 128 else 16) ≤ off.toNat)
      (hi : off.toNat ≤ (if second then 128 else 16) + 24) :
      InRegions (digestWrites fr second) (sp fr + off) 8 := by
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change (digestPtr fr second).toNat ≤ (sp fr + off).toNat ∧
      (sp fr + off).toNat + 8 ≤ (digestPtr fr second).toNat + 32 ∧
      (sp fr + off).toNat + 8 ≤ 2^64
    rw [dst, add _ (by omega)]
    omega
  have entry : a[4].get 64 = sp fr ∧ a[22] = ⟨1,0⟩ := by
    have atoms := live.atoms
    cases second
    case' false => cases input
    all_goals
      obtain ⟨rsp, df, _⟩ := atoms
      exact ⟨congrArg (Value.get 64) rsp, df⟩
  have ptr64 : a[3].get 64 = sp fr + 496 := congrArg (Value.get 64) ptr
  have prepared : ∃ b t, program.runBlock (dialect Extracted.programImage)
      ⟨finalizeAt second input,a,m⟩ =
        .call ⟨.l107a50,b,t⟩ ⟨keyAt second input,#v[],rfl,some ⟨64,digestReturn second input⟩⟩ ∧
      b[4] = ⟨64,sp fr - 8⟩ ∧ b[7] = ⟨64,sp fr + 496⟩ ∧ b[6] = ⟨64,digestPtr fr second⟩ ∧
      memLoad t (sp fr - 8) 64 = digestReturn second input ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (digestWrites fr second) := by
    have rsp := entry.1
    cases second
    case' false => cases input
    all_goals
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · simp only [finalizeAt, keyAt, digestReturn, seeded, Bool.false_eq_true, ite_false, ite_true]
        first
        | change program.runBlock _ ⟨.l1046c0, _, _⟩ = _
          cfg_eval [rsp, ptr64]
          iterate 5 (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1046c0)
        | change program.runBlock _ ⟨.l10432a, _, _⟩ = _
          cfg_eval [rsp, ptr64]
          iterate 5 (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10432a)
        | change program.runBlock _ ⟨.l1048d8, _, _⟩ = _
          cfg_eval [rsp, ptr64]
          iterate 5 (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1048d8)
        rfl
      · refine ⟨rfl, rfl, rfl, memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_⟩
        · rintro ⟨i,_⟩ hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · apply RamWriteFrame.memStore _ _ push
          repeat' apply RamWriteFrame.memStore _ _ (word _ (by decide) (by decide))
          exact RamWriteFrame.refl _ _
  obtain ⟨b, t, run, rsp, ctx, out, ret, keep, writes⟩ := prepared
  have pushedStack := stack.of_frame writes
  have retLow : (digestReturn second input).toNat < 2^32 := by
    cases second
    case' false => cases input
    all_goals
      simp only [digestReturn, seeded, Bool.false_eq_true, ite_false, ite_true]
      decide
  refine ⟨b, t, run, ⟨rsp, ctx, out, (keep 22 (by decide)).trans entry.2, ?_,
    pushedStack.sub (by omega) (by omega), by omega, by omega,
    pushedStack.readable.sub (by omega) (by omega), ret ▸ retLow,
    pushedStack.readable.sub (by omega) (by omega), pushedStack.sub (by omega) (by omega),
    by omega, by omega, env.imageAt (live.writes.trans writes ?_)⟩, ret, keep, writes⟩
  · intro i hi
    have sav : i.val ∈ Activation.calleeSavedNumbers := by
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rw [keep i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)]
    exact live.savedWidths i sav
  · intro r hr
    have low : fr.low.toNat = fr.rsp.toNat - 1920 := by rw [env.low, bottom]
    refine ⟨fr.region, List.mem_cons_self, ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · change fr.low.toNat ≤ (sp fr - 8).toNat ∧
        (sp fr - 8).toNat + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
    · obtain rfl := List.mem_singleton.mp h
      change fr.low.toNat ≤ (digestPtr fr second).toNat ∧
        (digestPtr fr second).toNat + 32 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega

end K256.Proofs.Signing.Nonce.Initialize.Update
