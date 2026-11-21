import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Compress.Blocks
import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare.Compress.Frame
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy
import K256.Proofs.Signing.UpdateV.Finalize.Memory
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Prepare

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private theorem compressIV (m : Ram) (s ret : BitVec 64) :
    Compression.StateAt (compressMemory m s ret) (s + 392) initialHash := by
  refine ⟨by decide +kernel, ?_⟩
  intro i hi
  have index : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases index with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero, compressMemory,
      Vector.getElem_ofFn] <;> segment_words [] <;> decide +kernel

theorem compress {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (live : Live (exitLabel second false) fr a m state) (slots : second = true → Slots fr m)
    (bytes : (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes m (UpdateV.keyPad state.key 0x36)) :
    ∃ b n, Verify.Core.Reaches (exitLabel second false) a m (head second true) b n ∧
      Live (head second true) fr b n state ∧ (second = true → Slots fr n) ∧
      b[0] = ⟨64, 3⟩ ∧ (second = true → b[13] = ⟨64, sp fr + 392⟩) ∧
      (⟨(pad fr second).toNat, 64⟩ : MemoryRegion).HasBytes n (UpdateV.keyPad state.key 0x36) ∧
      Compressed fr second n state.key := by
  let s := sp fr
  let child := compressMemory m s (compressRet second)
  have depth := env.depth
  have lim := env.limit
  have sn : s.toNat = fr.rsp.toNat - 712 := Absorb.spNat env
  have low : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have plus (off : Nat) (h : off ≤ 712) :
      (s + BitVec.ofNat 64 off).toNat = s.toNat + off := Absorb.spAddNat env off h
  have down₈ : (s - 8).toNat = s.toNat - 8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ s from (by omega : 8 ≤ s.toNat))
  have down : (s - 344).toNat = s.toNat - 344 := BitVec.toNat_sub_of_le
    (show (344 : BitVec 64) ≤ s from (by omega : 344 ≤ s.toNat))
  have p391 : (s + 391).toNat = s.toNat + 391 := plus 391 (by decide)
  have p392 : (s + 392).toNat = s.toNat + 392 := plus 392 (by decide)
  have p424 : (s + 424).toNat = s.toNat + 424 := plus 424 (by decide)
  have src : s.toNat ≤ (pad fr second).toNat ∧ (pad fr second).toNat + 64 ≤ s.toNat + 224 := by
    cases second
    · change s.toNat ≤ (s + 160).toNat ∧ (s + 160).toNat + 64 ≤ _
      have h : (s + 160).toNat = s.toNat + 160 := plus 160 (by decide)
      omega
    · change s.toNat ≤ (s + 48).toNat ∧ (s + 48).toNat + 64 ≤ _
      have h : (s + 48).toNat = s.toNat + 48 := plus 48 (by decide)
      omega
  have rsp : a[4] = ⟨64,s⟩ := by
    have atoms := live.atoms
    cases second <;> exact atoms.1
  obtain ⟨b,enter,brsp,bdst,bsrc,bcnt,b13,saved⟩ := compressCallBlock fr second
    (congrArg (Value.get 64) rsp) (Absorb.stackWritable env live.writes (p := s-8) (by omega) (by omega))
  have slot {off len : Nat} (lo : 391 ≤ off) (hi : off + len ≤ 432) :
      InRegions (compressRegions s) (s + BitVec.ofNat 64 off) len := by
    refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
    change (s + 391).toNat ≤ _ ∧ _ + len ≤ (s + 391).toNat + 41 ∧ _
    rw [plus off (by omega)]
    omega
  have push : InRegions (compressRegions s) (s - 8) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (s - 344).toNat ≤ _ ∧ _ + 8 ≤ (s - 344).toNat + 344 ∧ _
    omega
  have stage : RamWriteFrame m child (compressRegions s) := by
    unfold child compressMemory
    apply RamWriteFrame.memStore _ _ push
    repeat' apply RamWriteFrame.memStore _ _ (slot (by decide) (by decide))
    exact .refl _ _
  have outside : Outside (compressRegions s) (pad fr second) 64 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [compressRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · right; change (s-344).toNat + 344 ≤ _; omega
    · left; change _ ≤ (s+391).toNat; omega
  have writable {n : Ram} (w : RamWriteFrame m n (compressRegions s)) {p : BitVec 64} {k : Nat}
      (lo : fr.low.toNat ≤ p.toNat) (hi : p.toNat + k ≤ fr.rsp.toNat) :
      Writable Extracted.programImage n p k := (Absorb.stackWritable env live.writes lo hi).of_frame w
  have ret : memLoad child (s - 8) 64 = compressRet second :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have contract : Compression.Call b child (s-8) (s+392) (pad fr second) initialHash
      (UpdateV.keyPad state.key 0x36) := by
    have sz := UpdateV.keyPad_size state.key 0x36
    refine ⟨brsp,bdst,bsrc,by rw [sz]; exact bcnt,?_, compressIV _ _ _,by
      rw [sz]; exact UpdateV.Finalize.bytesAfter stage outside bytes, ?_, writable stage (by omega) (by omega),
      by omega, ?_, (writable stage (by omega) (by omega)).readable, ?_, .inr (by omega), .inr (by omega)⟩
    · intro i hi
      by_cases eq : i = 13
      · subst i; change b[13].width = 64; rw [b13]; cases second
        · exact live.savedWidths 13 (by decide)
        · rfl
      · have h : i.val ≠ 13 := fun e => eq (Fin.ext e)
        rw [saved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
        exact live.savedWidths i hi
    · rw [sz]; exact (writable stage (by omega) (by omega)).readable
    · rw [show s - 8 - 336 = s - 344 by bv_omega]
      exact writable stage (by omega) (by omega)
    · rw [ret]; cases second <;> decide
  obtain ⟨out, exec, post⟩ := Compression.execute contract
  have back := ParseSignature.exec_reaches_resume exec (compressResume second) []
    (by rw [post.tag,ret]; cases second <;> rfl)
  have compressed := stage.trans post.writes (by
    intro r hr
    simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_,List.mem_cons_self,?_⟩
      change (s-344).toNat ≤ (s-8).toNat - 336 ∧ (s-8).toNat - 336 + 336 ≤ (s-344).toNat + 344
      omega
    · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      change (s+391).toNat ≤ (s+392).toNat ∧ (s+392).toNat + 32 ≤ (s+391).toNat + 41
      omega)
  have restored : out.values[4] = ⟨64,s⟩ := by rw [post.rsp, BitVec.sub_add_cancel]
  obtain ⟨c, finish, idx, kept⟩ := compressResumeBlock s second (congrArg (Value.get 64) restored)
    (writable compressed (by omega) (by omega))
  have finalWrites := compressed.memStore (0 : BitVec 8) (slot (off := 391) (len := 1) (by decide) (by decide))
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,14,15,22,39,50,51]) : c[i] = a[i] := by
    rw [kept i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega),
      post.preserved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega), saved i hi]
  have r13 := (kept 13 (by decide)).trans ((post.preserved 13 (by decide)).trans b13)
  have final13 : c[13] = if second then ⟨64,sp fr + 392⟩ else a[13] := r13
  obtain ⟨alive, remaining⟩ := compressFrame second env live slots finalWrites
    ((kept 4 (by decide)).trans restored) keep r13
  refine ⟨c,_, .step (congrArg (Transfer.next _ []) enter)
    (back.trans (.step (congrArg (Transfer.next _ []) finish) (.refl _))),alive,remaining,idx,
    fun h => by simpa only [h,↓reduceIte] using final13,
    UpdateV.Finalize.bytesAfter finalWrites outside bytes,
    memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_⟩
  · exact ⟨post.state.1, post.state.2.write_apart _ _ (RangeApart.of_offsets rfl rfl (by decide))⟩
  · change memLoad (memStore out.store (s+391) (0 : BitVec 8)) (s+424) 64 = 1
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide)),
      post.writes.memLoad_eq]
    · unfold child compressMemory
      segment_words []
    · refine ⟨by omega, fun r hr => ?_⟩
      simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right; change (s-8).toNat - 336 + 336 ≤ (s+424).toNat; omega
      · right; change (s+392).toNat + 32 ≤ (s+424).toNat; omega

end K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
