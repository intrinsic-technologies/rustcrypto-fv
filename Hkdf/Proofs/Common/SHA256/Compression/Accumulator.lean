import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import Hkdf.Proofs.Common.SHA256.Compression.Support

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode05 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x05, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_05 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode05_run_of_acc (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_05 context true a b c d e f 0 = .ok 1 := by
  simp only [Select_Legacy_0_Opcode_05]
  rfl

theorem decodeLegacy0Opcode05_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_05 ip context).run s =
      (X86.Instructions.ADD_OrAX_IMMz (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_05
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_05 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode05_run_of_acc context)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_05_acc [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (0x05 :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.ADD_OrAX_IMMz (BitVec.add s.RIP 1#64)
        (legacyContext s.DS)).run (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x05 :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x05 :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x05, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode05 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode05_run_of_acc _ _ _ (hmode 2) hfeatures]

theorem add_eax_imm32_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 32)
    (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 32).run s = (.ok imm, t)) :
    (X86.Instructions.ADD_OrAX_IMMz ip ctx).run s =
      let dst : Operand 32 := .reg 0
      (.ok (), writeOutputs t dst (addSpec (dst.read s) (imm.signExtend 32)) 0
        (BitVec.add ip 4#64)) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_OrAX_IMMz
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    RAX => rax_run _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ _ (by decide) (by decide),
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ADD => add_operation _ 32 (by decide) _ _,
    Write_RAX => writeRAX_run _ 32 (by decide) _]

theorem add_eax_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (0x05 :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    let dst : Operand 32 := .reg 0
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      writeOutputs t dst (addSpec (dst.read t) (imm.signExtend 32)) 0
        (BitVec.add s.RIP 5#64))) := by
  have hdecode := decodeLegacy0_run_of_05_acc s h imm
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x05 :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x05 :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 2 h.fetchReady hc hlow' 32 (by decide) imm 1
    (immBytes_getElem?_append [0x05] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [add_eax_imm32_form _ _ (BitVec.add s.RIP 1#64) _ imm (legacyContext_operand_size s.DS) rfl himm,
    show BitVec.add (BitVec.add s.RIP 1#64) 4#64 = BitVec.add s.RIP 5#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x05 (immBytes 32 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

theorem add_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x05 :: immBytes 32 imm))
      (addR32Imm32Effect p 5 0 imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 5 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end Hkdf.Proofs.Common.SHA256.Compression
