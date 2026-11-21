import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Shift

set_option autoImplicit false

open P256.Proofs.Common.Instructions (sarFlags sarFlags_allows sarOracleAF sarOracleBits sarSpec)
open P256.Proofs.Common.Instructions.ByteLogic (readGPR8_run writeGPR8_run)

namespace P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions

open scoped X86.Runtime.Syntax

theorem shr_byte_four_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (htmode : In64BitMode t)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 4, t)) :
    (X86.Instructions.SHR_GPR8_IMMb ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 4) 4 (dst.read s))
        (shrOracleBits 4) (BitVec.add ip 1#64)) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SHR_GPR8_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHR => shr_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (htmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0OpcodeC0_shr_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 5#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_0_Opcode_C0 ip ctx).run s =
      (X86.Instructions.SHR_GPR8_IMMb (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_C0 ctx true a b c d e f modrm = .ok 3 := by
    simp [Select_Legacy_0_Opcode_C0, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_C0
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem shr_byte_four_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0xc0, modrm, 4]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t (.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8) (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 4) 4 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read t))
        (shrOracleBits 4) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 4, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeC0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeC0_shr_register _ _ _ (legacyContext s.DS) modrm.toBitVec hmod hreg (hm 3) hf fmod,
    shr_byte_four_form _ _ _ (legacyContext s.DS) (modrm.toBitVec.extractLsb' 0 3) (hm 3) (hm 4) (.inr hsmall) rfl fimm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xc0 [modrm,4]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def shrByteFourEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 ((Operand.reg dst : Operand 8).read s >>> 4)
        ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 4 ((Operand.reg dst : Operand 8).read s)) }

theorem shr_byte_four_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xc0,modrm,4]) (shrByteFourEffect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_byte_four_step s h modrm hmod hreg hsmall hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, shrSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact shrFlags_allows _ _ _ _ _

@[x86_local] theorem shrByteFourEffect_local (p : BitVec 64) (dst : BitVec 5) : Effect.Local (shrByteFourEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [shrByteFourEffect, shrFlags, h.read_reg]
    rfl
  · intro s
    simp [shrByteFourEffect, Write.Full, Operand.Full]

attribute [x86_compose] shrByteFourEffect

theorem sar_byte_four_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (htmode : In64BitMode t)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 4, t)) :
    (X86.Instructions.SAR_GPR8_IMMb ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle 4) 4 (dst.read s))
        (sarOracleBits 4) (BitVec.add ip 1#64)) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SAR_GPR8_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SAR => sar_byte_operation _ _ _ (by decide),
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (htmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0OpcodeC0_sar_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_0_Opcode_C0 ip ctx).run s =
      (X86.Instructions.SAR_GPR8_IMMb (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_C0 ctx true a b c d e f modrm = .ok 7 := by
    simp [Select_Legacy_0_Opcode_C0, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_C0
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem sar_byte_four_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0xc0, modrm, 4]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t (.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8) (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle 4) 4 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read t))
        (sarOracleBits 4) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 4, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeC0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeC0_sar_register _ _ _ (legacyContext s.DS) modrm.toBitVec hmod hreg (hm 3) hf fmod,
    sar_byte_four_form _ _ _ (legacyContext s.DS) (modrm.toBitVec.extractLsb' 0 3) (hm 3) (hm 4) (.inr hsmall) rfl fimm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xc0 [modrm,4]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def sarByteFourEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (((Operand.reg dst : Operand 8).read s).sshiftRight 4)
        ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) 4 ((Operand.reg dst : Operand 8).read s)) }

theorem sar_byte_four_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xc0,modrm,4]) (sarByteFourEffect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sar_byte_four_step s h modrm hmod hreg hsmall hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, sarSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact sarFlags_allows _ _ _ _ _

@[x86_local] theorem sarByteFourEffect_local (p : BitVec 64) (dst : BitVec 5) : Effect.Local (sarByteFourEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [sarByteFourEffect, sarFlags, h.read_reg]
    rfl
  · intro s
    simp [sarByteFourEffect, Write.Full, Operand.Full]

attribute [x86_compose] sarByteFourEffect

end P256.Proofs.Keygen.Multiply.ProjectiveRadix.Instructions
