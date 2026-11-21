import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Shift

set_option autoImplicit false

open P256.Proofs.Common.Instructions (sarFlags sarFlags_allows sarOracleAF sarOracleBits sarSpec)
open P256.Proofs.Common.Instructions.ByteLogic (readGPR8_run writeGPR8_run)

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions (sar_byte_operation)
open scoped X86.Runtime.Syntax

theorem decodeLegacy0_run_of_opcodeD0 [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xd0, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_D0 ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem sar_byte_one_form (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SAR_GPR8_ONE ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (sarSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (sarOracleAF s.oracle 1) 1 (dst.read s)) (sarOracleBits 1) ip) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SAR_GPR8_ONE
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    X86.Instructions.Operations.SAR => sar_byte_operation _ _ _ (by decide),
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0OpcodeD0_sar [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xf8, t)) :
    (Decode_Legacy_0_Opcode_D0 ip ctx).run s =
      (X86.Instructions.SAR_GPR8_ONE (BitVec.add ip 2#64) ctx 0).run t := by
  unfold Decode_Legacy_0_Opcode_D0
  decode_modrm_form s t ip hfetch hmode hf
    (show ∀ a b c d e f, Select_Legacy_0_Opcode_D0 ctx true a b c d e f 0xf8 = .ok 7
      from by intros; rfl)

theorem sar_al_one_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xd0, 0xf8]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 0 : Operand 8) (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle 1) 1 ((Operand.reg 0 : Operand 8).read t))
        (sarOracleBits 1) (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeD0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeD0_sar _ _ _ _ (hm 3) hf fmod,
    sar_byte_one_form _ _ _ _ (hm 3) (.inr (by change (0 : Nat) < 4; decide)) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xd0 [0xf8]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 3).of_cs_lma_eq rfl rfl)

def sarAlOneEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (((Operand.reg 0 : Operand 8).read s).sshiftRight 1)
        ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) 1 ((Operand.reg 0 : Operand 8).read s)) }

theorem sar_al_one_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xd0,0xf8]) (sarAlOneEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, sar_al_one_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, sarSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact sarFlags_allows _ _ _ _ _

attribute [x86_compose] sarAlOneEffect

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions
