import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Copy.Bounds

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private theorem padWord {fr : Activation} {second : Bool} (m : Ram) (k i : Nat)
    (hi : i < 8) (hk : k ≤ 8) (copied : 8 ≤ i+k) :
    memLoad (padWords fr second m k) (sp fr + BitVec.ofNat 64 (496 + 8*i)) 64 =
      memLoad m (sp fr + BitVec.ofNat 64 ((if second then 48 else 160) + 8*i)) 64 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [padWords]
    by_cases last : i = 7-k
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega))]
      exact ih (by omega) (by omega)

theorem copyHmac {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second true) fr a m state)
    (bytes : (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes m (UpdateV.keyPad state.key 0x5c))
    (hash : Compressed fr second m state.key) :
    UpdateV.HmacStateAt (copied fr second m) (context fr second) state.key ByteArray.empty := by
  let dst := sp fr + 496
  let words := padWords fr second m 8
  have base := copyBase env
  have depth := env.depth
  have limit := env.limit
  have dl : dst.toNat = (sp fr).toNat + 496 := copyAddr env 496 (by decide)
  have bottom : (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 :=
    BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)
  have wf := padWrites env m second 8 (by decide)
  have wr := padsFrame env m second 8 (by decide)
  have rd : Readable words dst 64 :=
    (((env.stack.of_frame live.writes).of_frame wr).readable).sub (by omega) (by omega)
  have pads : (⟨dst.toNat,64⟩ : MemoryRegion).HasBytes words (UpdateV.keyPad state.key 0x5c) := by
    have h := Common.hasBytes_of_word_copy (n := 8) bytes (UpdateV.keyPad_size _ _) rd
    refine ⟨UpdateV.keyPad_size _ _, (h ?_).2⟩
    intro i hi
    have w := padWord (fr := fr) (second := second) m 8 i hi (by decide) (by omega)
    cases second <;> simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      pad, Bool.false_eq_true, ite_false, ite_true, dst, words, BitVec.ofNat_add, BitVec.add_assoc] at w ⊢ <;> exact w
  have out (i n : Nat) (lo : 560 ≤ i) (hi : i + n ≤ 664) :
      Outside [⟨(sp fr).toNat+496,64⟩] (sp fr + BitVec.ofNat 64 i) n := by
    have pos := copyAddr env i (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (show (sp fr).toNat + 496 + 64 ≤ _ by omega)
  have inner : Compression.StateAt words (dst + 128)
      (compressBlocks initialHash (UpdateV.keyPad state.key 0x36)) := by
    have new := UpdateV.stateAt_memCopy_offset (dst := sp fr + 560) (src := sp fr + 328)
      (len := 104) (off := 64) (by decide) (by decide) (by
        rw [show sp fr + 328 + BitVec.ofNat 64 64 = sp fr + 392 by bv_omega]
        exact hash.hash)
    rw [show dst + 128 = sp fr + BitVec.ofNat 64 624 by dsimp [dst]; bv_omega]
    apply UpdateV.Finalize.stateAfter wf (out 624 32 (by decide) (by decide))
    exact (show sp fr + 560 + BitVec.ofNat 64 64 = sp fr + BitVec.ofNat 64 624 by bv_omega) ▸ new
  have field (off width i : Nat) (pos : off + width / 8 ≤ 104) (idx : i = 560 + off) :
      memLoad words (sp fr + BitVec.ofNat 64 i) width =
        memLoad m (sp fr + 328 + BitVec.ofNat 64 off) width := by
    rw [show memLoad words (sp fr + BitVec.ofNat 64 i) width = _ from
      wf.memLoad_eq (k := width) (out i (width / 8) (by omega) (by omega))]
    rw [show sp fr + BitVec.ofNat 64 i = sp fr + 560 + BitVec.ofNat 64 off by
      rw [idx, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl]
    exact Sec1.Parser.Result.memLoad_memCopy m _ _ (by decide : 104 ≤ 2^64) pos
  have empty : ByteArray.empty.size < 64 := by decide
  have hmac : UpdateV.HmacStateAt words dst state.key ByteArray.empty := by
    refine ⟨pads, ?_, ?_, ?_, ?_⟩
    · rw [UpdateV.remainderBytes_keyPad_short _ _ _ empty]
      exact ⟨rfl,fun i => False.elim (Nat.not_lt_zero _ i.isLt)⟩
    · rw [show dst + 127 = sp fr + BitVec.ofNat 64 623 by dsimp [dst]; bv_omega,
        field 63 8 623 (by decide) rfl]
      rw [show sp fr + 328 + BitVec.ofNat 64 63 = sp fr + 391 by bv_omega]
      exact hash.used
    · rw [UpdateV.compressBlocks_keyPad_short _ _ _ _ empty]
      exact inner
    · rw [show dst + 160 = sp fr + BitVec.ofNat 64 656 by dsimp [dst]; bv_omega,
        field 96 64 656 (by decide) rfl]
      rw [show sp fr + 328 + BitVec.ofNat 64 96 = sp fr + 424 by bv_omega]
      exact hash.count
  have slot := copySlot env
  have push : RamWriteFrame words (pushed fr second m) [⟨(sp fr - 8).toNat,8⟩] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, Nat.le_refl _,
      Nat.le_refl _, by change (sp fr - 8).toNat + 8 ≤ 2^64; omega⟩
  apply UpdateV.HmacStateAt.memCopy
  apply UpdateV.Finalize.hmacAfter push _ hmac
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  exact Or.inr (show (sp fr - 8).toNat + 8 ≤ dst.toNat by omega)

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
