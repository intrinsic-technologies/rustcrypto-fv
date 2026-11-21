import K256.Proofs.Verify.Hash.Update.Short
import K256.Proofs.Verify.Hash.Update.Compress

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper Verify.LIR

theorem long {s : RamState} {key msg sig : ByteArray} {a : Vector Value 53} {m : Ram}
    {hash : Array UInt32} (compress : Compresses)
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (cur : Memory s m)
    (rsp : a[4].get 64 = localSp s) (rbx : a[3].get 64 = s.regValue .rdx)
    (r14 : a[14].get 64 = s.regValue .rsi)
    (widths : ∀ i : Fin 53, i.val ∈ [5,13,14] → a[i].width = 64)
    (df : a[22].get 1 = 0) (hs : Compression.StateAt m (localSp s+312) hash)
    (size : 64 ≤ msg.size) :
    ∃ b m', segment .l10311e a m .l103170 b m' ∧ Updated s msg hash a m b m' := by
  let sp := localSp s
  let n := BitVec.ofNat 64 (msg.size % 64)
  let src := s.regValue .rsi + BitVec.ofNat 64 (64 * (msg.size / 64))
  have len : n.toNat = msg.size % 64 := Nat.mod_eq_of_lt (by have := Nat.mod_lt msg.size (by decide : 0 < 64); omega)
  have less : n.toNat < 64 := len ▸ Nat.mod_lt _ (by decide)
  obtain ⟨b,t,front,w1,state,count,bsp,bn,bsrc,keep⟩ :=
    compressPrefix compress call cur rsp rbx r14 widths hs size
  let marked := memStore t (sp+311) (n.setWidth 8)
  let pushed := memStore marked (sp-8) (0x103170 : BitVec 64)
  have markAddr : sp + 311 = stackPtr s - 225 := by dsimp only [sp,localSp]; bv_omega
  have pushAddr : sp - 8 = stackPtr s - 544 := by dsimp only [sp,localSp]; bv_omega
  have cur1 := advance call cur w1
  have wm := writable (len := 1) (off := 225) call cur1 markAddr (by decide) (by decide) (by decide)
  have markOk : StoreOk Extracted.programImage t (sp+311) 1 0x103154 8 :=
    ParseSignature.storeOk_of_codeRange (off := 0) wm
      (fun x hx => Common.fnCode_subset_programImage x (code_l103154 x hx)) (by decide)
  have w2 : RamWriteFrame m marked (footprint s) :=
    w1.memStore _ (frameSlot (off := 225) call markAddr (by decide) (by decide))
  have cur2 := advance call cur w2
  have ws := writable (len := 8) (off := 544) call cur2 pushAddr (by decide) (by decide) (by decide)
  have pushOk : StoreOk Extracted.programImage marked (sp-8) 8 0x10316a 6 :=
    ParseSignature.storeOk_of_codeRange (off := 22) ws
      (fun x hx => Common.fnCode_subset_programImage x (code_l103154 x hx)) (by decide)
  have w3 : RamWriteFrame m pushed (footprint s) :=
    w2.memStore _ (frameSlot (off := 544) call pushAddr (by decide) (by decide))
  have ret : memLoad pushed (sp-8) 64 = 0x103170 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨got,target⟩ := Sec1.Wrapper.memcpy_target_load (inputMemory call cur2.frame).2.2.2
  have called := longCopy (congrArg (Value.get 64) bsp) (congrArg (Value.get 64) bn)
    (congrArg (Value.get 64) bsrc) markOk pushOk got target
  obtain ⟨out,run,copy,tag,sp',kept,bytes⟩ := copyRemainder (a := b) (src := src) (n := n)
    call (advance call cur w3) rfl len ((congrArg (Value.get 1) (keep 22 (by decide))).trans df)
    (by rw [ret]; decide)
  have back := ParseSignature.exec_reaches_resume run (returnFrame .l103170 0x103170) []
    (by rw [tag,ret]; rfl)
  have w4 : RamWriteFrame m out.store (footprint s) := by
    rw [copy]
    apply Sec1.Wrapper.Copy.memCopy_frame w3
    exact frameSlot (off := 288) call (by dsimp only [localSp]; bv_omega) (by decide) (by omega)
  refine ⟨out.values,out.store,front.trans (.step (congrArg (Transfer.next _ []) called) back),
    w4,sp',fun i hi => (kept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (keep i hi), (congrArg Value.width ((kept 12 (by decide)).trans bn)), ?_, bytes, ?_, ?_⟩
  · rw [copy]
    apply stateStore
    · exact stateStore (stateStore state _ (by apply RangeApart.of_offsets rfl rfl; decide)) _
        (by apply RangeApart.of_offsets (addr_sub _ _) rfl; decide)
    · rw [show 8 * n.toNat / 8 = n.toNat by omega]
      apply RangeApart.of_offsets rfl rfl
      exact ⟨by change n.toNat ≤ 64; omega, by decide⟩
  · rw [copy]
    change memLoad (memStore pushed (sp+248) _) (sp+311) 8 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
      apply RangeApart.of_offsets rfl rfl
      exact ⟨by change 8*n.toNat/8 ≤ 63; omega, by decide⟩)]
    dsimp only [pushed,marked]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
      apply RangeApart.of_offsets (addr_sub _ _) rfl; decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    exact (BitVec.ofNat_toNat 8 n).symm.trans (congrArg (BitVec.ofNat 8) len)
  · rw [copy]
    change memLoad (memStore pushed (sp+248) _) (sp+344) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
      apply RangeApart.of_offsets rfl rfl
      exact ⟨by change 8*n.toNat/8 ≤ 96; omega, by decide⟩)]
    dsimp only [pushed,marked]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
      apply RangeApart.of_offsets (addr_sub _ _) rfl; decide)]
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_offsets rfl rfl; decide)]
    exact count

end K256.Proofs.Verify.Hash.Update
