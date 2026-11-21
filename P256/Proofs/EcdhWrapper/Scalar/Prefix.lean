import P256.Proofs.EcdhWrapper.Scalar.Prefix.Entry

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prefix_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ t, CheckedPrefix initial t secret := by
  obtain ⟨first,decoded,cleared,called,t,entry,decodedResult,clearEffectH,selectedAgrees,
    selectedResult,calledRsp,calledOutput,⟨n,run⟩,rip,rsp,r14,valid,scalar⟩ :=
    decode_select_correct hb hm call
  have decodedRsp : stackPtr decoded = stackPtr initial-504 := by
    have sp : stackPtr decoded = stackPtr first+8 := decodedResult.rsp
    rw [sp,entry.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have cg := clear_agrees decodedRsp clearEffectH
  have middle := cg.trans selectedAgrees
  obtain ⟨decodedFrame,decodedMxcsr,decodedFp87,slots⟩ := entry.prefix_facts call decodedResult
  obtain ⟨_,_,pointers,count,lengths⟩ := entry.result_registers call decodedResult
  have growth : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome :=
    fun a ha => selectedResult.allocated a (middle.grow a (decodedResult.allocated a (entry.allocated a ha)))
  obtain ⟨u,⟨m,nonzeroRun⟩,ripU,rspU,al,value,saved,bindingsSupported,machine,direction,
    loaded,grow,mxcsr,fp87,nonzeroFrame,nonzeroAgrees⟩ :=
    Nonzero.correct hb hm call selectedResult.bindingsSupported selectedResult.machine
      selectedResult.directionFlag selectedResult.loaded growth rip rsp r14 scalar
  have middleFrame : MemoryWriteFrame decoded called (wrapperRegions ecdhDiffieHellman initial) := by
    apply middle.memoryWriteFrame
    intro c hc a ha
    simp only [selectComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact ha.elim
    all_goals refine ⟨callStack ecdhDiffieHellman initial,by simp [wrapperRegions],?_⟩
    · exact stack_component_within call.stackAvailable.1 (offset := 432) (by decide) (by decide) ha
    · exact stack_component_within call.stackAvailable.1 (offset := 440) (by decide) (by decide) ha
    · exact stack_component_within call.stackAvailable.1 (offset := 448) (by decide) (by decide) ha
    · exact stack_component_within call.stackAvailable.1 (offset := 456) (by decide) (by decide) ha
    · exact stack_component_within call.stackAvailable.1 (offset := 512) (by decide) (by decide) ha
  have selectedFrame := selectedResult.stack_frame call.stackAvailable.1 calledRsp calledOutput
    (savedBytes := 48) (by decide) (by decide) (by decide) (by decide)
  have frame := memoryWriteFrame_trans
    (memoryWriteFrame_trans (memoryWriteFrame_trans decodedFrame middleFrame)
      (prefix_work_frame call.stackAvailable.1 selectedFrame))
    (prefix_work_frame call.stackAvailable.1 nonzeroFrame)
  have word (offset : Nat) (range : offset ≤ 48 ∨ offset = 464 ∨ offset = 472) :
      memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad decoded.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
    rw [prefix_nonzero_word call.stackAvailable.1 nonzeroAgrees range]
    have keep : memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad called.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
      apply memLoad_congr
      intro i hi
      apply memByte_congr
      exact selectedResult.stack_byte call.stackAvailable.1 calledRsp calledOutput
        (frameOffset := 504) (outputOffset := 264) (len := 8) (by decide) (by decide) (by omega) (by omega)
        (by rcases range with h | rfl | rfl <;> omega) hi
    rw [keep]
    exact prefix_middle_word call.stackAvailable.1 middle range
  obtain ⟨savedWords,returnWord⟩ := entry.saved_words call decodedResult
  refine ⟨u,⟨⟨n+m,run.trans nonzeroRun⟩,ripU,rspU,al,?_,?_,?_,?_,value,frame,
    bindingsSupported,machine,direction,loaded,grow,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [saved .rbp (by simp)]
    exact valid
  · exact (saved .r12 (by simp)).trans ((selectedResult.calleeSaved .r12 (by simp)).trans
      ((middle.read (n := 64) (r := 12) (by simp [selectComponents])).trans pointers))
  · exact (saved .r13 (by simp)).trans ((selectedResult.calleeSaved .r13 (by simp)).trans
      ((middle.read (n := 64) (r := 13) (by simp [selectComponents])).trans count))
  · exact (saved .r15 (by simp)).trans ((selectedResult.calleeSaved .r15 (by simp)).trans
      ((middle.read (n := 64) (r := 15) (by simp [selectComponents])).trans lengths))
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (word reg.2 (.inl bound)).trans (savedWords reg member)
  · have h := word 0 (.inl (by decide))
    simp only [BitVec.sub_zero] at h
    exact h.trans returnWord
  · exact (word 472 (.inr (.inr rfl))).trans (slots false)
  · exact (word 464 (.inr (.inl rfl))).trans (slots true)
  · exact mxcsr.trans (selectedResult.mxcsr.trans
      ((middle.mxcsr (by simp [selectComponents])).trans decodedMxcsr))
  · exact fp87.trans (selectedResult.fp87.trans
      ((middle.fcw (by simp [selectComponents])).trans decodedFp87))

end P256.Proofs.EcdhWrapper.Scalar
