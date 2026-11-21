import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions

set_option autoImplicit false

namespace P256.Proofs.HashToCurve.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Encoding.Parser.TagOps

theorem shr_low8_cl_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s)
    (hsmall : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHR_GPR8_CL ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (shrSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shrOracleAF s.oracle c) c (dst.read s)) (shrOracleBits c) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHR_GPR8_CL
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ hsmall _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.SHR => shr_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ hsmall _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decode_d2_ea [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xea, t)) :
    (Decode_Legacy_0_Opcode_D2 ip ctx).run s =
      (X86.Instructions.SHR_GPR8_CL (BitVec.add ip 2#64) ctx 2).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_D2 ctx true a b c d e f 0xea = .ok 3 := by
    rfl
  unfold Decode_Legacy_0_Opcode_D2
  decode_modrm_form s t ip hfetch hmode hf hsel

def shrDlClState (s : RamState) : RamState :=
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  afterStep s 2 fun t => writeOutputs t (.reg 2 : Operand 8)
    (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS) (oracleBit t.oracle)
      (shrOracleAF t.oracle c) c ((Operand.reg 2 : Operand 8).read t))
    (shrOracleBits c) (BitVec.add s.RIP 2#64)

theorem shr_dl_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xd2, 0xea]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (shrDlClState s)) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := X86Proofs.decodeLegacy0_run_of_opcodeD2 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decode_d2_ea _ _ _ _ (hm 3) hf fmod,
    shr_low8_cl_form _ _ _ _ (hm 3) (by change 2 < 4; decide) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xd2 [0xea]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hm 3).of_cs_lma_eq rfl rfl)

def shrDlClEffect (p : BitVec 64) (s : RamState) : Effect :=
  let x := (Operand.reg 2 : Operand 8).read s
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  { rip := p + 2
    writes := [⟨(Operand.reg 2 : Operand 64),
      mergeGPR 8 (x >>> c) ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) c x) }

theorem shr_dl_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xd2, 0xea])
      (shrDlClEffect p) := by
  rintro s h hcode rfl
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  let out := fun t : RamState => shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
    (oracleBit t.oracle) (shrOracleAF t.oracle c) c ((Operand.reg 2 : Operand 8).read t)
  refine ⟨shrDlClState s,
    shr_dl_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 2 out (shrOracleBits c) (BitVec.add s.RIP 2#64), ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 2 (.reg 2) out (shrOracleBits c) _, ?_,
    StatusFlagsOutcome.allows_store ?_ _,
    AgreesExcept.afterStep_writeOutputs s 2 2 out (shrOracleBits c) _⟩
  · change (Operand.reg 2 : Operand 64).read (shrDlClState s) = _
    rw [shrDlClState, Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, shrSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact shrFlags_allows _ _ _ _ _

end P256.Proofs.HashToCurve.Wrapper.Finish
