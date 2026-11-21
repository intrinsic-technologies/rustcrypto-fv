import AesGcm.Proofs.AES16.KeySchedule.InputMemory
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Calls

namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Generation

set_option maxHeartbeats 1000000 in
theorem key_input_reaches (use256 later : Bool) (hlater : later = true → use256 = true)
    (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hMemory : Generation.MemoryReady use256 code mem (args[4].get 64))
    (hTypes : GPRsTyped args) (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hbuffer : args[14].get 64 = args[4].get 64 + (if use256 then 12 else 8))
    (hkey : Readable mem (args[12].get 64) (if use256 then 32 else 16)) :
    ∃ output : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if later then .l105825 else if use256 then .l1057f1 else .l1043a4), args, mem⟩, []⟩
        ⟨⟨(if later then .l105856 else if use256 then .l105825 else .l1043d2),
          output.values, output.store⟩, []⟩ ∧
      output.values[4].get 64 = args[4].get 64 ∧
      output.values[12] = args[12] ∧ output.values[14] = args[14] ∧
      output.values[15].get 64 = (if use256 && !later then (8 : BitVec 64) else args[15].get 64) ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 5, 13, 22, 39, 50, 51] →
        output.values[r] = args[r]) ∧
      GPRsTyped output.values ∧
      RamWriteFrame mem output.store
        [span (args[4].get 64 - 248) 248,
          span (args[4].get 64 + (if use256 then 288 else 200)) 16,
          span (args[4].get 64 + (if use256 then 12 else 8) + (if later then 16 else 0)) 16] ∧
      WordsAt output.store
        (args[4].get 64 + (if use256 then 12 else 8) + (if later then 16 else 0)) 16
        (Vector.ofFn (Fixslice16.encode
          (Fixslice.memoryBlock mem (args[12].get 64 + (if later then 16 else 0))))) := by
  have hroom := hMemory.hroom
  have hlim := Generation.stack_limit hMemory
  have hlow := Generation.stack_sub_toNat hMemory
  have hstack : Writable code mem (args[4].get 64 - 8) (if use256 then 312 else 224) := by
    apply hMemory.hstack.sub
    all_goals rw [hlow]
    all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  obtain ⟨callee, cont, hc, hl, ht, hg, hm, hc4, hc7, hc6, hc2,
      hc12, hc14, hc15, hc3, hc5, hc13, hc22, hc39, hc50, hc51, hcT⟩ :=
    key_input_call use256 later hlater code hcode args mem hbuffer hstack hkey
  let av : Values Value Reg.count := callee.arguments
  let sp := args[4].get 64
  let ret : BitVec 64 := if later then 0x105856 else if use256 then 0x105825 else 0x1043d2
  let src := args[12].get 64 + (if later then 16 else 0)
  let raw := sp + (if use256 then 288 else 200)
  let prepared := memStore (memStore mem (raw + 8) (memLoad mem (src + 8) 64))
    raw (memLoad mem src 64)
  have hRaw : RamWriteFrame mem prepared [span raw 16] := by
    dsimp only [prepared, raw, sp]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    all_goals runtime_finish [span]
  have hRawWithin : RegionsWithin [span raw 16]
      [span (sp - 248) (if use256 then 608 else 512)] := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨_, List.Mem.head _, ?_, ?_⟩
    all_goals dsimp only [span, raw, sp]
    all_goals rw [hlow]
    all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hPrepared := Generation.memoryReady_of_frame hMemory hRaw hRawWithin
  have hSetup := inputMemory_frame use256 later args mem hstack.readable
  have hAllWithin : RegionsWithin
      [span (sp - 8) 8, span raw 16]
      [span (sp - 248) (if use256 then 608 else 512)] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.Mem.head _, ?_, ?_⟩
      all_goals dsimp only [span, sp]
      all_goals rw [hlow]
      all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    · exact hRawWithin _ (List.Mem.head _)
  have hPushed := Generation.memoryReady_of_frame hMemory hSetup hAllWithin
  have hcTypes := hcT hTypes
  have hF39 : av[39] = ⟨32, av[39].get 32⟩ := by rw [hc39, h39]; rfl
  have hF50 : av[50] = ⟨16, av[50].get 16⟩ := by rw [hc50, h50]; rfl
  have hF51 : av[51] = ⟨16, av[51].get 16⟩ := by rw [hc51, h51]; rfl
  obtain ⟨output, hExec, hTag, hDone, hoTypes, hFrame, hWords⟩ :=
    Generation.Native.pushed_call_exec LIR.lifted code .l109ff0 LIR.Fn109ff0.frameInfo
      (fun fr ↦ [span fr.rdi 16])
      (fun fr m ↦ fr.rsi = 8 ∧ Readable m fr.rdx 16 ∧ Writable code m fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16) ∧
        (callStack fr).Disjoint (span fr.rdx 16) ∧
        (span fr.rdi 16).Disjoint (span fr.rdx 16))
      (fun fr m ↦ WordsAt m fr.rdi 16
        (Vector.ofFn (Fixslice16.encode (Fixslice.memoryBlock fr.original fr.rdx))))
      (AES16.input_call code hcode) prepared av sp ret hPrepared hc4 hcTypes
      hF39 hF50 hF51 (hc22.trans hDF)
      (by cases use256 <;> cases later <;> decide) (by decide) (by decide)
      (input_call_pre hPushed av ret hc4 hc7 hc6 hc2)
  obtain ⟨ho4, hoPreserved⟩ := Generation.Native.pushed_call_done
    LIR.Fn109ff0.frameInfo rfl rfl code _ av sp ret (sp - 248) output hc4 hcTypes
    hF39 hF50 hF51 (hc22.trans hDF) hDone
  have he : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    cases callee with
    | mk label values store => cases hl; cases hm; exact hExec
  have ha : cont.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hg, hTag, dialect]
    cases use256 <;> cases later <;> rfl
  have hReach := CFGCall.exec_reaches_resume he cont [] ha
  have hv := CFGCall.resume_arguments cont output
  have htarget : (cont.resume output).label =
      (if later then .l105856 else if use256 then .l105825 else .l1043d2) := ht
  have hmem : (cont.resume output).store = output.store := rfl
  have hloc : cont.resume output =
      ⟨(if later then .l105856 else if use256 then .l105825 else .l1043d2),
        output.values, output.store⟩ := by
    generalize cont.resume output = loc at hv htarget hmem ⊢
    cases loc with
    | mk label values store =>
      dsimp only at hv htarget hmem
      cases htarget; cases hv; cases hmem; rfl
  rw [hloc] at hReach
  refine ⟨output, ?_, ?_, (hoPreserved 12 (by decide)).trans hc12,
    (hoPreserved 14 (by decide)).trans hc14, ?_, ?_, hoTypes, ?_, ?_⟩
  · apply Star.step (b := ⟨callee, [cont]⟩)
    · change (LIR.program.runBlock (dialect code) _).next (dialect code) [] = _
      rw [hc]; rfl
    · exact hReach
  · rw [ho4]; rfl
  · exact (congrArg (Value.get 64) (hoPreserved 15 (by decide))).trans hc15
  · rintro ⟨r, hrBound⟩ hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hoPreserved 3 (by decide)).trans hc3
    · exact (hoPreserved 5 (by decide)).trans hc5
    · exact (hoPreserved 13 (by decide)).trans hc13
    · exact (hoPreserved 22 (by decide)).trans hc22
    · exact (hoPreserved 39 (by decide)).trans hc39
    · exact (hoPreserved 50 (by decide)).trans hc50
    · exact (hoPreserved 51 (by decide)).trans hc51
  · have hSetup' : RamWriteFrame mem (inputMemory use256 later args mem)
        [span (sp - 248) 248, span raw 16,
          span (sp + (if use256 then 12 else 8) + (if later then 16 else 0)) 16] := by
      apply (RamWriteFrame.refl _ _).trans hSetup
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.Mem.head _, ?_, ?_⟩
        all_goals dsimp only [span, sp]
        all_goals rw [hlow]
        all_goals bv_omega
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, Nat.le_refl _⟩
    apply hSetup'.trans hFrame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.Mem.head _, ?_, ?_⟩
      · exact Nat.le_refl _
      · simp only [Activation.region, activationOfValues, av, hc4, span]
        dsimp only [sp]
        rw [hlow]
        bv_omega
    · simp only [activationOfValues, av, hc7]
      exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
        Nat.le_refl _, Nat.le_refl _⟩
  · change WordsAt output.store (av[7].get 64) 16
      (Vector.ofFn (Fixslice16.encode
        (Fixslice.memoryBlock (inputMemory use256 later args mem) (av[2].get 64)))) at hWords
    rw [hc7, hc2, inputMemory_block] at hWords
    exact hWords

end AesGcm.Proofs.Machine.AES16.KeySchedule
