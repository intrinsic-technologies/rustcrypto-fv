import P256.Proofs.Common.Instructions.Setb.Form
import X86Proofs.Instructions.Mov.Step
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Parser

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

open scoped X86.Runtime.Syntax

theorem decodeLegacy0_run_of_opcodeB0 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xb0, u)) (hmode : In64BitMode u)
    (hf : DecoderFeatures u) :
    (Decode_Legacy_0 ip context).run s =
      some ((X86.Instructions.MOV_GPR8_IMMb_B0 (BitVec.add ip 1#64) context 0xb0).run u) := by
  have hdispatch : (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_B0 ip context 0xb0).run u) := by
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

theorem mov_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (opcode : BitVec 8) (imm : BitVec 8)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hrex : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true) :
    (X86.Instructions.MOV_GPR8_IMMb_B0 ip ctx opcode).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3)) : Operand 8)
        imm (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPR8_IMMb_B0
  simp only [writeResult, Operand.write]
  spec_run [Mem_Fetch => hfetch,
    X86.Instructions.Operations.MOV => mov_operation _ 8 _]
  dsimp only
  rw [hrex]
  have hv : BitVec.ofInt (Int.toNat 8) imm.toInt = imm := BitVec.ofInt_toInt
  rw [hv]
  exact writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)

theorem mov_r8b_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : UInt8) (hcode : BytesAt s s.RIP [0x41, 0xb0, imm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg 8 : Operand 8) imm.toBitVec (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x41, 0xb0, imm] := hcode
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xb0, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeB0 _ _ _ (rexContext s.DS 0x41) rfl fop (hmode 3) hf
  rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _,
    mov_r8_imm8_form _ _ _ _ _ _ fimm (hmode 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x41 0xb0 [imm] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def movR8bImm8Effect (p : BitVec 64) (imm : UInt8) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 8 : Operand 64),
      mergeGPR 8 imm.toBitVec ((Operand.reg 8 : Operand 64).read s)⟩] }

theorem mov_r8b_imm8_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0xb0, imm])
      (movR8bImm8Effect p imm) := by
  intro s h hcode hp
  subst p
  refine ⟨_, mov_r8b_imm8_step s h imm hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _, ?_⟩
  refine ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult _ _ _ _ _⟩
  change (Operand.reg 8 : Operand 64).read
    (afterStep s 3 fun t => writeResult t (.reg 8 : Operand 8) imm.toBitVec (BitVec.add s.RIP 3#64)) = _
  rw [Operand.read_afterStep]
  simp [writeResult, Operand.read, Operand.write, afterFetches, beforeFetch, resetStepFields]

end P256.Proofs.Common.Encoding.Parser
