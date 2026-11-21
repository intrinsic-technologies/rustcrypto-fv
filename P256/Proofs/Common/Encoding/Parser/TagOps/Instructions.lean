import X86Proofs.Instructions.MovStore.Decode
import P256.Proofs.Common.Instructions.Setb.Form
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Shr.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Parser.TagOps

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shr_r8_cl_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHR_GPR8_CL ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (shrSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) (shrOracleAF s.oracle c) c (dst.read s)) (shrOracleBits c) ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHR_GPR8_CL
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.SHR => shr_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem and_r8_r8_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.AND_GPR8_GPR8_20 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (andSpec (oracleBit s.oracle) (dst.read s) (src.read s)) 1 ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.AND_GPR8_GPR8_20
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem cmp_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.CMP_GPR8_IMMb_80r7 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t (cmpSpec (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPR8_IMMb_80r7
  simp only [Operand.read, writeFlagsOutputs, oracleSkip_zero]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

theorem decodeLegacy0_run_of_opcodeD2 [Bindings]
    (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD2, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_D2 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0OpcodeD2_run [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xe8, t)) :
    (Decode_Legacy_0_Opcode_D2 ip ctx).run s =
      (X86.Instructions.SHR_GPR8_CL (BitVec.add ip 2#64) ctx 0).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_D2 ctx true a b c d e f 0xe8 = .ok 3 := by
    rfl
  unfold Decode_Legacy_0_Opcode_D2
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem decodeLegacy0Opcode20_run [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xc0, t)) :
    (Decode_Legacy_0_Opcode_20 ip ctx).run s =
      (X86.Instructions.AND_GPR8_GPR8_20 (BitVec.add ip 2#64) ctx 0 0).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_20 ctx true a b c d e f 0xc0 = .ok 1 := by
    rfl
  unfold Decode_Legacy_0_Opcode_20
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem decodeLegacy0Opcode80_run [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xf8, t)) :
    (Decode_Legacy_0_Opcode_80 ip ctx).run s =
      (X86.Instructions.CMP_GPR8_IMMb_80r7 (BitVec.add ip 2#64) ctx 0).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_80 ctx true a b c d e f 0xf8 = .ok 16 := by
    rfl
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf hsel

def shrR8bClState (s : RamState) : RamState :=
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  afterStep s 3 fun t => writeOutputs t (.reg 8 : Operand 8)
    (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS) (oracleBit t.oracle)
      (shrOracleAF t.oracle c) c ((Operand.reg 8 : Operand 8).read t))
    (shrOracleBits c) (BitVec.add s.RIP 3#64)

def andR8bAlState (s : RamState) : RamState :=
  afterStep s 3 fun t => writeOutputs t (.reg 8 : Operand 8)
    (andSpec (oracleBit t.oracle) ((Operand.reg 8 : Operand 8).read t)
      ((Operand.reg 0 : Operand 8).read t)) 1 (BitVec.add s.RIP 3#64)

def cmpR8bOneState (s : RamState) : RamState :=
  afterStep s 4 fun t => writeFlagsOutputs t
    (cmpSpec ((Operand.reg 8 : Operand 8).read t) 1) 0 (BitVec.add s.RIP 4#64)

theorem shr_r8b_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x41, 0xD2, 0xe8]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (shrR8bClState s)) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeD2 _ _ _ (rexContext s.DS 0x41) rfl fop (hmode 3)
  rw [decodeLegacy0OpcodeD2_run _ _ _ _ (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, shr_r8_cl_form _ _ _ _ (hmode 4) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x41 0xD2 [0xe8] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem and_r8b_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x41, 0x20, 0xc0]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (andR8bAlState s)) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode20 _ _ _ (rexContext s.DS 0x41) rfl fop (hmode 3)
  rw [decodeLegacy0Opcode20_run _ _ _ _ (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, and_r8_r8_form _ _ _ _ _ (hmode 4) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x41 0x20 [0xc0] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem cmp_r8b_one_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x41, 0x80, 0xf8, 1]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (cmpR8bOneState s)) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have fimm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok 1, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  have hd := decodeLegacy0_run_of_opcode80 _ _ _ (rexContext s.DS 0x41) rfl fop (hmode 3)
  rw [decodeLegacy0Opcode80_run _ _ _ _ (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, cmp_r8_imm8_form _ _ _ _ _ _ (hmode 4) rfl rfl fimm,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x41 0x80 [0xf8, 1] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

def shrR8bClEffect (p : BitVec 64) (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 8).read s
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  { rip := p + 3
    writes := [⟨(Operand.reg 8 : Operand 64),
      mergeGPR 8 (x >>> c) ((Operand.reg 8 : Operand 64).read s)⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) c x) }

def andR8bAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 8 : Operand 8).read s &&& (Operand.reg 0 : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg 8 : Operand 64),
      mergeGPR 8 r ((Operand.reg 8 : Operand 64).read s)⟩]
    flags := some (andFlags r) }

def cmpR8bOneEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 8 : Operand 8).read s) 1)) }

theorem shr_r8b_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0xd2, 0xe8])
      (shrR8bClEffect p) := by
  rintro s h hcode rfl
  let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
  let out := fun t : RamState => shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
    (oracleBit t.oracle) (shrOracleAF t.oracle c) c ((Operand.reg 8 : Operand 8).read t)
  refine ⟨shrR8bClState s,
    shr_r8b_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 8 out (shrOracleBits c) (BitVec.add s.RIP 3#64), ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 3 (.reg 8) out (shrOracleBits c) _, ?_,
    StatusFlagsOutcome.allows_store ?_ _,
    AgreesExcept.afterStep_writeOutputs s 3 8 out (shrOracleBits c) _⟩
  · change (Operand.reg 8 : Operand 64).read (shrR8bClState s) = _
    rw [shrR8bClState, Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, shrSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact shrFlags_allows _ _ _ _ _

theorem and_r8b_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x20, 0xc0])
      (andR8bAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, and_r8b_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 8 _ 1 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 8 _ 1 _⟩
  · change (Operand.reg 8 : Operand 64).read (andR8bAlState s) = _
    rw [andR8bAlState, Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, andSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem cmp_r8b_one_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x80, 0xf8, 1])
      (cmpR8bOneEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r8b_one_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 0 _, ?_⟩
  refine ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Encoding.Parser.TagOps
