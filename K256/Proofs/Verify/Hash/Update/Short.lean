import K256.Proofs.Sec1.Wrapper.Calls
import K256.Proofs.Verify.Hash.Update.Remainder
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper Verify.LIR

theorem short {s : RamState} {key msg sig : ByteArray} {a : Vector Value 53} {m : Ram}
    {hash : Array UInt32} (call : ValidCall verifyingKeyVerify s [key,msg,sig]) (cur : Memory s m)
    (rsp : a[4].get 64 = localSp s) (rbx : a[3].get 64 = s.regValue .rdx)
    (r14 : a[14].get 64 = s.regValue .rsi) (r12 : a[12].width = 64)
    (df : a[22].get 1 = 0) (hs : Compression.StateAt m (localSp s+312) hash)
    (zero : memLoad m (localSp s+344) 64 = 0) (size : msg.size < 64) :
    ∃ b m', segment .l103101 a m .l103170 b m' ∧ Updated s msg hash a m b m' := by
  let sp := localSp s
  let src := s.regValue .rsi
  let n := s.regValue .rdx
  let pushed := memStore m (sp-8) (0x103115 : BitVec 64)
  have nlen : n.toNat = msg.size := call.lengthArgumentsMatchInputs.2.1
  have less : n.toNat < 64 := by omega
  have q := Nat.div_eq_of_lt size
  have r := Nat.mod_eq_of_lt size
  have ws := writable (p := sp-8) (off := 544) (len := 8) call cur
    (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide) (by decide)
  have push : StoreOk Extracted.programImage m (sp-8) 8 0x10310f 6 :=
    ParseSignature.storeOk_of_codeRange (off := 14) ws
      (fun x hx => Common.fnCode_subset_programImage x (code_l103101 x hx)) (by decide)
  obtain ⟨got,target⟩ := Sec1.Wrapper.memcpy_target_load (inputMemory call cur.frame).2.2.2
  have called := shortCall rsp rbx r14 push got target
  have slot : InRegions (footprint s) (sp-8) 8 := frameSlot (off := 544) call
    (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide)
  have w1 : RamWriteFrame m pushed (footprint s) := (RamWriteFrame.refl m _).memStore _ slot
  have ret : memLoad pushed (sp-8) 64 = 0x103115 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨out,run,copy,tag,sp',kept,bytes⟩ := copyRemainder (a := a) (src := src) (n := n)
    call (advance call cur w1) (by rw [q]; simp [src]) (by rwa [r]) df (by rw [ret]; decide)
  have size' : (8*n.toNat)/8 = n.toNat := by omega
  have w2 : RamWriteFrame m out.store (footprint s) := by
    rw [copy]
    apply Sec1.Wrapper.Copy.memCopy_frame w1
    exact frameSlot (off := 288) call (by dsimp only [localSp]; bv_omega) (by decide) (by omega)
  have wc := writable (p := sp+311) (off := 225) (len := 1) call (advance call cur w2)
    (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide) (by decide)
  have tailStore : StoreOk Extracted.programImage out.store (sp+311) 1 0x103115 7 :=
    ParseSignature.storeOk_of_codeRange (off := 0) wc
      (fun x hx => Common.fnCode_subset_programImage x (code_l103115 x hx)) (by decide)
  have returned := shortReturn (by rw [sp']; rfl : out.values[4].get 64 = sp)
    ((congrArg (Value.get 64) (kept 3 (by decide))).trans rbx) tailStore
  refine ⟨out.values,memStore out.store (sp+311) (n.setWidth 8),?_,?_⟩
  · have back := ParseSignature.exec_reaches_resume run (returnFrame .l103115 0x103115) []
      (by rw [tag,ret]; rfl)
    exact .step (congrArg (Transfer.next _ []) called) (back.trans (.single (congrArg (Transfer.next _ []) returned)))
  · refine ⟨w2.memStore _ (frameSlot (off := 225) call
      (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide)), sp',
      fun i hi => kept i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega), (congrArg Value.width (kept 12 (by decide))).trans r12,
      ?_, ?_, ?_, ?_⟩
    · change Compression.StateAt _ _ (compressBlocksFrom hash msg 0 (msg.size/64))
      rw [q]
      apply stateStore
      · rw [copy]
        apply stateStore
        · exact stateStore hs _ (by apply RangeApart.of_offsets (addr_sub _ _) rfl; decide)
        · rw [size']
          apply RangeApart.of_offsets rfl rfl
          change n.toNat ≤ 64 ∧ _
          exact ⟨by omega, by decide⟩
      · apply RangeApart.of_offsets rfl rfl
        decide
    · apply bytesStore bytes
      apply RangeApart.of_offsets rfl rfl
      exact ⟨by decide, by change msg.size % 64 ≤ 63; omega⟩
    · rw [memLoad_memStore_same _ _ _ (by decide) (by decide), r, ← nlen]
      exact (BitVec.ofNat_toNat 8 n).symm
    · rw [copy]
      unfold memCopy
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_offsets rfl rfl; decide),
        memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          rw [size']; apply RangeApart.of_offsets rfl rfl; exact ⟨by change n.toNat ≤ 96; omega, by decide⟩)]
      unfold pushed
      rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by apply RangeApart.of_offsets (addr_sub _ _) rfl; decide), zero, q]
      rfl

end K256.Proofs.Verify.Hash.Update
