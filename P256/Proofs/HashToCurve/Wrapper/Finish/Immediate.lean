import P256.Proofs.Common.Encoding.Serialize.Tail.Prepare.Encode.Immediate

set_option autoImplicit false

namespace P256.Proofs.HashToCurve.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Encoding.Serialize
open scoped X86.Runtime.Syntax

theorem decode_b2 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xb2, u)) (hmode : In64BitMode u)
    (hf : DecoderFeatures u) :
    (Decode_Legacy_0 ip context).run s =
      some ((X86.Instructions.MOV_GPR8_IMMb_B0 (BitVec.add ip 1#64) context 0xb2).run u) := by
  have hdispatch : (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_B0 ip context 0xb2).run u) := by
    unfold Decode_Legacy_0
    rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
    rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
    repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
    rfl
  rw [hdispatch]
  apply congrArg some
  unfold Decode_Legacy_0_Opcode_B0
  refine (decoderSelect_run_noModRM u _ _ 1 hmode hf (by intros; rfl)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := u) rfl).trans ?_
  exact specM_bind_pure_unit_run _ u

theorem mov_dl_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : UInt8) (hcode : BytesAt s s.RIP [0xb2, imm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeResult t (.reg 2 : Operand 8) imm.toBitVec (BitVec.add s.RIP 2#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xb2, imm] := hcode
  have fop := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0
    (by simp) (by decide)
  change (Mem_Fetch (BitVec.add s.RIP 0#64) 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xb2, afterFetches (beforeFetch s) 2) at fop
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop
  have fimm : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decode_b2 _ _ _ (legacyContext s.DS) rfl fop (hmode 2) hf
  rw [prepare_mov_low8_imm8_form _ _ _ _ _ _ fimm (hmode 3) rfl (by change 2 < 4; decide),
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xb2 [imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

def movDlImm8Effect (p : BitVec 64) (imm : UInt8) (s : RamState) : Effect :=
  { rip := p + 2
    writes := [⟨(Operand.reg 2 : Operand 64),
      mergeGPR 8 imm.toBitVec ((Operand.reg 2 : Operand 64).read s)⟩] }

theorem mov_dl_imm8_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xb2, imm])
      (movDlImm8Effect p imm) := by
  intro s h hcode hp
  subst p
  refine ⟨_, mov_dl_imm8_step s h imm hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 2 _ _ _, ?_⟩
  refine ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult _ _ _ _ _⟩
  change (Operand.reg 2 : Operand 64).read
    (afterStep s 2 fun t => writeResult t (.reg 2 : Operand 8) imm.toBitVec (BitVec.add s.RIP 2#64)) = _
  rw [Operand.read_afterStep]
  simp [writeResult, Operand.read, Operand.write, afterFetches, beforeFetch, resetStepFields]

end P256.Proofs.HashToCurve.Wrapper.Finish
