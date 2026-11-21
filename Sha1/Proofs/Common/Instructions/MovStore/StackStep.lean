import Sha1.Proofs.Common.Instructions.MovStore.StackForm
import X86Proofs.Instructions.Push.Step
import X86Proofs.Instructions.Call.Step

namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

private theorem push_start [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) ∧ (afterFetches (beforeFetch s) k).SS = userStackSegment :=
  ⟨h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables, h.cpu.ss⟩

theorem push_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 0 (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 1#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_push s h op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 2
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op [] hop.legacyOpcode hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem push_r64_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) (hcode : BytesAt s s.RIP [rex, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 2#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_rex_push s h rex op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 3
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op [] hrex hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem call_rel32_step [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 32)
    (hcode : BytesAt s s.RIP (0xE8 :: immBytes 32 disp)) (hlow : s.RIP.toNat + 5 ≤ 2^32)
    (htarget : (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      callState (callFrom false t (BitVec.add s.RIP 5#64)) (BitVec.add s.RIP 5#64)
        (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xE8 :: immBytes 32 disp) := hcode
  have hlow' : s.RIP.toNat + (0xE8 :: immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xE8, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 32).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 32 (by decide) disp 1
      (immBytes_getElem?_append [0xE8] disp) (by simp) (by decide)
  obtain ⟨hd, hss⟩ := call_start h 6
  have hdecode := decodeLegacy0_run_of_opcodeE8 _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeE8_run_of_call _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [call_rel32_form _ _ _ _ disp rfl rfl f2 (hmode 6) hd hss
    (by rw [add_ofNat_add]; exact htarget) (hw.of_external_eq rfl), add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h _ (immBytes 32 disp)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

end Sha1.Proofs.Common.Instructions.MovStore
