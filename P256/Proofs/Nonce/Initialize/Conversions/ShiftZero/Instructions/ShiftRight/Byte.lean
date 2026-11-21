import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Shift

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftRight

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess
open P256.Proofs.Common.Instructions.ByteLogic (readGPR8_run writeGPR8_run)
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
open scoped X86.Runtime.Syntax

theorem shr_byte_six_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (htmode : In64BitMode t)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 6, t)) :
    (X86.Instructions.SHR_GPR8_IMMb ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 6) 6 (dst.read s))
        (shrOracleBits 6) (BitVec.add ip 1#64)) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SHR_GPR8_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHR => shr_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (htmode.of_cs_lma_eq rfl rfl)]

theorem shr_al_six_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xc0, 0xe8, 6]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t (.reg 0 : Operand 8) (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 6) 6 ((Operand.reg 0 : Operand 8).read t))
        (shrOracleBits 6) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 6, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeC0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeC0_shr _ _ _ _ (hm 3) hf fmod,
    shr_byte_six_form _ _ _ _ _ (hm 3) (hm 4) (.inr (by change (0 : Nat) < 4; decide)) rfl fimm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xc0 [0xe8,6]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def shrAlSixEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 ((Operand.reg 0 : Operand 8).read s >>> 6)
        ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((Operand.reg 0 : Operand 8).read s)) }

theorem shr_al_six_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xc0,0xe8,6]) (shrAlSixEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, shr_al_six_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, shrSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact shrFlags_allows _ _ _ _ _

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftRight
