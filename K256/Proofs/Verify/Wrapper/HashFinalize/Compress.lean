import K256.Proofs.Verify.Wrapper.HashFinalize.State

namespace K256.Proofs.Verify.Wrapper.HashFinalize

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Hash.FinalBlocks

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

theorem compressBlock {hash : Array UInt32} (compress : Hash.Update.Compresses)
    (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (h : State initial a m p r s msg hash) (last : Bool) (block : ByteArray)
    (size : block.size = 64)
    (bytes : (⟨(localSp initial+160).toNat,64⟩ : MemoryRegion).HasBytes
      (callMemory last m (localSp initial) (a[15].get 64)) block) :
    ∃ b t, Core.Reaches (callSite last) a m (resumeSite last) b t ∧
      State initial b t p r s msg (Hash.compressBlocks hash block) := by
  let sp := localSp initial
  let child := callMemory last m sp (a[15].get 64)
  obtain ⟨depth,low⟩ := Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 :=
    Common.stackOffset call.stackAvailable (by decide)
  have dep : 344 ≤ sp.toNat := by omega
  have room : sp.toNat+224 ≤ 2^32 := by omega
  have bounds (reg) (hr : reg ∈ footprint sp) :
      (stackPtr initial).toNat - 13000 ≤ reg.start ∧ reg.start + reg.size ≤ sp.toNat + 224 := by
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  have next {u v : Ram} (mem : Memory initial u) (writes : RamWriteFrame u v (footprint sp)) :
      Memory initial v := mem.advance call writes (by
        intro reg hr; obtain ⟨lo,hi⟩ := bounds reg hr; exact ⟨lo,by omega⟩)
  have writes := preparedWrites last m sp (a[15].get 64) dep room
  have mem := next h.memory writes
  have stack : Writable Extracted.programImage m (sp-8) 232 :=
    Hash.Update.writable (off := 544) call h.memory (by dsimp only [sp,localSp]; bv_omega)
      (by decide) (by decide) (by decide)
  obtain ⟨b,step,rsp,rdi,rsi,rdx,preserved⟩ := prepareCall last a m sp
    (congrArg (Value.get 64) h.rsp) (congrArg (Value.get 64) h.rbx) stack
  have readRet : (sp-8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : Word) ≤ sp from (show 8 ≤ sp.toNat by omega))
  have natAdd (k : Nat) (hk : k ≤ 224) : (sp+BitVec.ofNat 64 k).toNat = sp.toNat+k := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have word := preparedReturn last m sp (a[15].get 64)
  have contract : Hash.Compression.Call b child (sp-8) (sp+72) (sp+160) hash block := by
    refine ⟨rsp,rdi,rsi,by rw [size]; exact rdx,?_,
      preparedState last m sp (a[15].get 64) h.state dep room,by simpa only [size] using bytes,
      ?_,?_,by omega,?_,?_,?_,Or.inr ?_,Or.inr ?_⟩
    · intro ⟨i,hi⟩ hi'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rw [preserved _ (by decide +revert)]
      · exact congrArg Value.width h.rbx
      · exact congrArg Value.width h.rbp
      · exact h.r12Width
      · exact congrArg Value.width h.r13
      · exact h.r14Width
      · exact congrArg Value.width h.length
    · rw [size]
      exact (Hash.Update.writable (off := 376) call mem (by dsimp only [sp,localSp]; bv_omega)
        (by decide) (by decide) (by decide)).readable
    · exact Hash.Update.writable (off := 464) call mem (by dsimp only [sp,localSp]; bv_omega)
        (by decide) (by decide) (by decide)
    · exact Hash.Update.writable (off := 880) call mem (by dsimp only [sp,localSp]; bv_omega)
        (by decide) (by decide) (by decide)
    · exact (Hash.Update.writable (off := 544) call mem (by dsimp only [sp,localSp]; bv_omega)
        (by decide) (by decide) (by decide)).readable
    · change (memLoad (callMemory last m sp _) _ 64).toNat < _
      rw [word]; cases last <;> decide
    · have := natAdd 72 (by decide); change (sp-8).toNat + 8 ≤ (sp+BitVec.ofNat 64 72).toNat; omega
    · have := natAdd 160 (by decide); change (sp-8).toNat ≤ (sp+BitVec.ofNat 64 160).toNat; omega
  obtain ⟨out,exec,post⟩ := compress contract
  have back := ParseSignature.exec_reaches_resume exec (resumeFrame last) [] (by
    rw [post.tag,word]; cases last <;> rfl)
  have allWrites := writes.trans post.writes (calleeWithin sp dep room)
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := (post.preserved i hi).trans (preserved i hi)
  refine ⟨out.values,out.store,.step (congrArg (Transfer.next _ []) step) back,
    ⟨next h.memory allWrites, ?_,(keep 5 (by decide)).trans h.rbp,
    (keep 13 (by decide)).trans h.r13,(keep 22 (by decide)).trans h.df,
    (congrArg Value.width (keep 12 (by decide))).trans h.r12Width,
    (congrArg Value.width (keep 39 (by decide))).trans h.mxcsr,
    (congrArg Value.width (keep 50 (by decide))).trans h.ftw,
    (congrArg Value.width (keep 51 (by decide))).trans h.fcw⟩,
    h.operands.afterHashWrites call allWrites ?_,post.state,(keep 3 (by decide)).trans h.rbx,
    (congrArg Value.width (keep 14 (by decide))).trans h.r14Width,(keep 15 (by decide)).trans h.length⟩
  · rw [post.rsp]; congr 1; change sp-8+8 = sp; bv_omega
  · intro reg hr; have := (bounds reg hr).2; change _ ≤ sp.toNat+352; omega

end K256.Proofs.Verify.Wrapper.HashFinalize
