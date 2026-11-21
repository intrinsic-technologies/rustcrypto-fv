import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Hash.Update.Lengths
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper Verify.LIR

abbrev Compresses := ∀ {a : Vector Value 53} {m : Ram} {sp dst src : BitVec 64}
    {hash : Array UInt32} {input : ByteArray}, Compression.Call a m sp dst src hash input →
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1218e0, a, m⟩, []⟩ out ∧
      Compression.Returned a m sp dst (compressBlocks hash input) out

local macro "compress_reg " idx:term " := " bits:term : tactic =>
  `(tactic| exact congrArg (Value.get 64) (show (compressArgs _ _ _ _)[$idx] = ⟨64, $bits⟩ by
    simp only [compressArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]))

theorem compressPrefix {s : RamState} {key msg sig : ByteArray} {a : Vector Value 53} {m : Ram}
    {hash : Array UInt32} (compress : Compresses)
    (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (cur : Memory s m)
    (rsp : a[4].get 64 = localSp s) (rbx : a[3].get 64 = s.regValue .rdx)
    (r14 : a[14].get 64 = s.regValue .rsi)
    (widths : ∀ i : Fin 53, i.val ∈ [5,13,14] → a[i].width = 64)
    (hs : Compression.StateAt m (localSp s+312) hash) (size : 64 ≤ msg.size) :
    let sp := localSp s
    ∃ b m', segment .l10311e a m .l103154 b m' ∧ RamWriteFrame m m' (footprint s) ∧
      Compression.StateAt m' (sp+312) (compressBlocks hash msg) ∧
      memLoad m' (sp+344) 64 = BitVec.ofNat 64 (msg.size/64) ∧
      b[4] = ⟨64,sp⟩ ∧ b[12] = ⟨64,BitVec.ofNat 64 (msg.size%64)⟩ ∧
      b[15] = ⟨64,s.regValue .rsi + BitVec.ofNat 64 (64*(msg.size/64))⟩ ∧
      ∀ i : Fin 53, i.val ∈ [5,13,22,39,50,51] → b[i] = a[i] := by
  dsimp only
  let sp := localSp s
  let src := s.regValue .rsi
  let n := s.regValue .rdx
  let dst := sp + 312
  let child := compressArgs a sp src n
  let counted := memStore m (sp+344) (n >>> 6)
  let pushed := memStore counted (sp-8) (0x103154 : BitVec 64)
  have nlen : n.toNat = msg.size := call.lengthArgumentsMatchInputs.2.1
  obtain ⟨_,readable⟩ := messageMemory call cur
  have nsmall : n.toNat < 2^63 := by have := readable.low; omega
  have count : n >>> 6 = BitVec.ofNat 64 (msg.size / 64) := by rw [block_count, nlen]
  have countEq : sp + 344 = stackPtr s - (192 : BitVec 64) := by
    dsimp only [sp,localSp]
    bv_omega
  have retEq : sp - 8 = stackPtr s - (544 : BitVec 64) := by
    dsimp only [sp,localSp]
    bv_omega
  have dstEq : dst = stackPtr s - (224 : BitVec 64) := by
    dsimp only [dst,sp,localSp]
    bv_omega
  have stackEq : sp - 8 - 336 = stackPtr s - (880 : BitVec 64) := by
    dsimp only [sp,localSp]
    bv_omega
  have slotCount : InRegions (footprint s) (sp+344) 8 :=
    frameSlot (off := 192) call countEq (by decide) (by decide)
  have slotRet : InRegions (footprint s) (sp-8) 8 :=
    frameSlot (off := 544) call retEq (by decide) (by decide)
  have writesCount : RamWriteFrame m counted (footprint s) :=
    (RamWriteFrame.refl m _).memStore _ slotCount
  have writesPush : RamWriteFrame m pushed (footprint s) := writesCount.memStore _ slotRet
  have memCount := advance call cur writesCount
  have memPush := advance call cur writesPush
  have code := fun x hx => Common.fnCode_subset_programImage x (code_l10311e x hx)
  have guardCount : StoreOk Extracted.programImage m (sp+344) 8 0x103141 8 :=
    ParseSignature.storeOk_of_codeRange (off := 35)
      (writable (off := 192) call cur countEq (by decide) (by decide) (by decide)) code (by decide)
  have guardPush : StoreOk Extracted.programImage counted (sp-8) 8 0x10314f 5 :=
    ParseSignature.storeOk_of_codeRange (off := 49)
      (writable (off := 544) call memCount retEq (by decide) (by decide) (by decide)) code (by decide)
  have called := longCall rsp rbx r14 guardCount guardPush
  have hashPush : Compression.StateAt pushed dst hash := by
    apply stateStore (stateStore hs _ (RangeApart.of_offsets rfl rfl (by decide)))
    exact RangeApart.of_offsets (addr_sub _ _) rfl (by decide)
  have retWord : memLoad pushed (sp-8) 64 = 0x103154 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have saved : ∀ i : Fin 53, i.val ∈ [5,13,22,39,50,51] → child[i] = a[i] := by
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [child, compressArgs, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  obtain ⟨bytes,read⟩ := messageMemory call memPush
  obtain ⟨depth,low⟩ := stackBounds call
  have natDst : dst.toNat = (stackPtr s).toNat - 224 := by
    rw [dstEq]
    exact Common.stackOffset call.stackAvailable (by decide)
  have natRet : (sp-8).toNat = (stackPtr s).toNat - 544 := by
    rw [retEq]
    exact Common.stackOffset call.stackAvailable (by decide)
  have natCount : (sp+344).toNat = (stackPtr s).toNat - 192 := by
    rw [countEq]
    exact Common.stackOffset call.stackAvailable (by decide)
  have contract : Compression.Call child pushed (sp-8) dst src hash msg := by
    refine ⟨?_,?_,?_,?_,?_,hashPush,bytes,read,?_,?_,?_,?_,?_,?_,?_⟩
    · compress_reg 4 := sp-8
    · compress_reg 7 := sp+312
    · compress_reg 6 := src
    · refine Eq.trans ?_ count
      compress_reg 2 := n >>> 6
    · intro ⟨i,hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [child, compressArgs, Fin.getElem_fin, Vector.getElem_set,
        Nat.reduceEqDiff, ↓reduceIte]
      · exact widths 5 (by decide)
      · exact widths 13 (by decide)
      · exact widths 14 (by decide)
    · exact writable (off := 224) call memPush dstEq (by decide) (by decide) (by decide)
    · omega
    · exact writable (off := 880) call memPush stackEq (by decide) (by decide) (by decide)
    · exact (writable (off := 544) call memPush retEq (by decide) (by decide) (by decide)).readable
    · rw [retWord]
      decide
    · exact Or.inr (by omega)
    · change (s.regValue .rsi).toNat + msg.size ≤ (sp-8).toNat - 336 ∨ (sp-8).toNat ≤ (s.regValue .rsi).toNat
      rcases messageApart call (show 0 < msg.size by omega) with apart | apart <;> omega
  obtain ⟨out,exec,post⟩ := compress contract
  have back := ParseSignature.exec_reaches_resume exec (returnFrame .l103154 0x103154) []
    (by rw [post.tag,retWord]; rfl)
  have within : RegionsWithin (Compression.footprint (sp-8) dst) (footprint s) := by
    intro r hr
    simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rcases hr with rfl | rfl
    · change (stackPtr s).toNat - 880 ≤ (sp-8).toNat - 336 ∧
        (sp-8).toNat - 336 + 336 ≤ (stackPtr s).toNat - 880 + 696
      omega
    · change (stackPtr s).toNat - 880 ≤ dst.toNat ∧
        dst.toNat + 32 ≤ (stackPtr s).toNat - 880 + 696
      omega
  refine ⟨out.values,out.store,.step (congrArg (Transfer.next _ []) called) back,
    writesPush.trans post.writes within,post.state,?_,?_,?_,?_,?_⟩
  · have outside : Outside (Compression.footprint (sp-8) dst) (sp+344) 8 := by
      refine ⟨by omega, fun r hr => ?_⟩
      simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (by change (sp-8).toNat - 336 + 336 ≤ _; omega)
      · exact Or.inr (by change dst.toNat + 32 ≤ _; omega)
    rw [post.writes.memLoad_eq outside]
    unfold pushed counted
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_sub _ _) rfl (by decide)),
      memLoad_memStore_same _ _ _ (by decide) (by decide), count]
  · rw [post.rsp]
    congr 1
    bv_omega
  · refine (post.preserved 12 (by decide)).trans ?_
    change child[(12 : Nat)] = _
    simp only [child, compressArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.mk 64) ((tail_length n).trans (congrArg (fun k => BitVec.ofNat 64 (k % 64)) nlen))
  · refine (post.preserved 15 (by decide)).trans ?_
    change child[(15 : Nat)] = _
    simp only [child, compressArgs, Vector.getElem_set, ↓reduceIte]
    apply congrArg (Value.mk 64)
    rw [full_length _ nsmall, nlen, BitVec.add_comm]
  · intro ⟨i,hi⟩ h
    have h' : (⟨i,hi⟩ : Fin 53).val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      omega
    exact (post.preserved ⟨i,hi⟩ h').trans (saved ⟨i,hi⟩ h)

end K256.Proofs.Verify.Hash.Update
