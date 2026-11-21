import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.Digest.Restore
import K256.Proofs.Signing.UpdateV.Finalize.Callee
import K256.Proofs.Signing.UpdateV.Finalize.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

private theorem digestContextOutside (fr : Activation) {input : Input} (env : Environment fr input)
    (second : Bool) : Outside (digestWrites fr second) (sp fr + 496) 168 := by
  have dep := env.depth
  have lim := env.limit
  have base : (sp fr).toNat = fr.rsp.toNat - 712 :=
    BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from by change 712 ≤ fr.rsp.toNat; omega)
  have sub : (sp fr - 8).toNat = (sp fr).toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp fr from by change 8 ≤ (sp fr).toNat; omega)
  have add (k : BitVec 64) (h : k.toNat ≤ 496) : (sp fr + k).toNat = (sp fr).toNat + k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [add _ (by decide)]; change (sp fr).toNat + 496 + 168 ≤ 2^64; omega, fun r hr => Or.inr ?_⟩
  rcases List.mem_cons.mp hr with rfl | h
  · change (sp fr - 8).toNat + 8 ≤ (sp fr + 496).toNat
    rw [sub, add _ (by decide)]
    change (sp fr).toNat - 8 + 8 ≤ (sp fr).toNat + 496
    omega
  · obtain rfl := List.mem_singleton.mp h
    cases second <;> simp only [digestPtr, Bool.false_eq_true, ite_false, ite_true]
      <;> rw [add _ (by decide), add _ (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega

private theorem digestMessageSmall {fr : Activation} {input : Input} {state : State}
    (second : Bool) (env : Environment fr input) (roundOk : second = true → seeded input = true)
    {m : Ram} (bytes : StateAt m fr.rdi state) :
    (message second input state).size % 64 < 56 := by
  have valueSize : state.value.size = 32 := bytes.value.1
  cases input with
  | empty =>
    simp only [message, seed, ByteArray.size_append, valueSize]
    cases second with
    | false => decide
    | true => exact False.elim (Bool.noConfusion (roundOk rfl))
  | seeded s h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hs, hh⟩ := env.slices
    have ss : s.size = 32 := hs.1
    have sh : h.size = 32 := hh.1
    simp only [message, seed, ByteArray.size_append, valueSize, ss, sh]
    cases second <;> decide

theorem finalizeRoundContext {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (finalizeAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (ptr : a[3] = ⟨64, sp fr + 496⟩)
    (ctx : UpdateV.HmacStateAt m (sp fr + 496) state.key (message second input state)) :
    ∃ b n, Verify.Core.Reaches (finalizeAt second input) a m (keyAt second input) b n ∧
      Live (keyAt second input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      ParseSignature.ArgumentWidths b ∧
      (⟨(digestPtr fr second).toNat, 32⟩ : MemoryRegion).HasBytes n (nextKey second input state) := by
  obtain ⟨b,t,push,call,ret,bKeep,stores⟩ := digestCall second env live ptr
  have keySize : state.key.size = 32 := live.bytes.key.1
  obtain ⟨out,run,tag,rsp,regs,keep,writes,digest,widths⟩ := UpdateV.Finalize.execute call
    (UpdateV.Finalize.hmacAfter stores (digestContextOutside fr env second) ctx)
    (by omega) (digestMessageSmall second env roundOk live.bytes)
  have same (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) : out.values[i] = a[i] := by
    by_cases hs : i.val ∈ Activation.calleeSavedNumbers
    · have idx : ∃ j : Fin 6, (#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[j] = i := by
        rcases i with ⟨i, bound⟩
        simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
        all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩
      obtain ⟨j, hj⟩ := idx
      subst i
      have reg := regs j
      rw [bKeep _ hi] at reg
      rw [reg]
      have w := live.savedWidths _ hs
      generalize a[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[j]] = v at w ⊢
      cases v with | mk n bits => cases w; rw [Value.get_mk]
    · apply (keep i ?_).trans (bKeep i hi)
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hs hi ⊢
      omega
  obtain ⟨result,slots'⟩ := digestRestore second env live slots stores writes
    (by simpa only [BitVec.sub_add_cancel] using rsp) same
  exact ⟨_,_,Verify.reachesOfCall push run (ret ▸ tag),result,slots',widths,digest⟩

end K256.Proofs.Signing.Nonce.Initialize.Update
