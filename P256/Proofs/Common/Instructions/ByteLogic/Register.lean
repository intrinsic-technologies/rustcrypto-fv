import P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.Output.RegisterLogic
import X86Proofs.Instructions.Add.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteLogic

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.OutputInstructions
  (decodeLegacy0Opcode08_run_of_register)
open P256.Proofs.Common.Field.FieldNeg.Instructions (orSpec orFlags or_operation)

theorem decodeLegacy0_run_of_opcode00 [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_00 ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0Opcode00_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_0_Opcode_00 ip ctx).run s =
      (X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_00 ctx true a b c d e f modrm = .ok 1 := by
    simp [Select_Legacy_0_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem add_bl_bl_form (s : RamState) (ip : BitVec 64) (hmode : In64BitMode s) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip (legacyContext s.DS) 3 3).run s =
      (.ok (), writeOutputs s (.reg 3 : Operand 8)
        (addSpec ((Operand.reg 3 : Operand 8).read s)
          ((Operand.reg 3 : Operand 8).read s)) 0 ip) := by
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write, legacyContext]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => X86Proofs.writeGPR8_run_of_low _ _ (by decide) _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem add_bl_bl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x00,0xdb]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 3 : Operand 8)
        (addSpec ((Operand.reg 3 : Operand 8).read t)
          ((Operand.reg 3 : Operand 8).read t)) 0 (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop,fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode00 _ _ s.RIP (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0Opcode00_run_of_register _ _ s.RIP (legacyContext s.DS) _ rfl (hm 3) hf fmod] at hd
  erw [add_bl_bl_form _ (BitVec.add s.RIP 2#64) (hm 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x00 [0xdb]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

def addBlBlEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 3 : Operand 8).read s + (Operand.reg 3 : Operand 8).read s
  { rip := p+2
    writes := [⟨(Operand.reg 3 : Operand 64),mergeGPR 8 r ((Operand.reg 3 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 3 : Operand 8).read s)
      ((Operand.reg 3 : Operand 8).read s)).2) }

theorem add_bl_bl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x00,0xdb]) (addBlBlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, add_bl_bl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem or_bl_al_form (s : RamState) (ip : BitVec 64) (hmode : In64BitMode s) :
    (X86.Instructions.OR_GPR8_GPR8_08 ip (legacyContext s.DS) 0 3).run s =
      (.ok (), writeOutputs s (.reg 3 : Operand 8)
        (orSpec (oracleBit s.oracle) ((Operand.reg 3 : Operand 8).read s)
          ((Operand.reg 0 : Operand 8).read s)) 1 ip) := by
  unfold X86.Instructions.OR_GPR8_GPR8_08
  simp only [Operand.read, writeOutputs, Operand.write, legacyContext]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ hmode,
    X86.Instructions.Operations.OR => or_operation _ 8 (by decide) _ _,
    Write_GPR8 => X86Proofs.writeGPR8_run_of_low _ _ (by decide) _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem or_bl_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x08,0xc3]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 3 : Operand 8)
        (orSpec (oracleBit t.oracle) ((Operand.reg 3 : Operand 8).read t)
          ((Operand.reg 0 : Operand 8).read t)) 1 (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop,fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode08 _ _ s.RIP (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0Opcode08_run_of_register _ _ s.RIP (legacyContext s.DS) _ rfl (hm 3) hf fmod] at hd
  erw [or_bl_al_form _ (BitVec.add s.RIP 2#64) (hm 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x08 [0xc3]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

def orBlAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 3 : Operand 8).read s ||| (Operand.reg 0 : Operand 8).read s
  { rip := p+2
    writes := [⟨(Operand.reg 3 : Operand 64),mergeGPR 8 r ((Operand.reg 3 : Operand 64).read s)⟩]
    flags := some (orFlags r) }

theorem or_bl_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x08,0xc3]) (orBlAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, or_bl_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, orSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact ⟨rfl,rfl,trivial,rfl,rfl,rfl⟩

theorem addBlBlEffect_components (p : BitVec 64) (s : RamState) :
    (addBlBlEffect p s).components = [.reg 3, .flags, .rip] := rfl

theorem orBlAlEffect_components (p : BitVec 64) (s : RamState) :
    (orBlAlEffect p s).components = [.reg 3, .flags, .rip] := rfl

theorem add_r8_r8_rex_form (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (addSpec (dst.read s) (src.read s)) 0 ip) := by
  have hctx : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hctx]
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => X86Proofs.writeGPR8_run_of_rex _ _ _
      (hmode.of_cs_lma_eq rfl rfl)]

theorem add_r8_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x00, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (addSpec (dst.read t) (src.read t)) 0 (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode00 _ _ _ (rexContext s.DS rex.toBitVec) rfl fop (hm 3)
  rw [decodeLegacy0Opcode00_run_of_register _ _ _ _ _ hmod (hm 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, add_r8_r8_rex_form _ _ _ _ _ (hm 4) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x00 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def addR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem add_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x00, modrm])
      (addR8R8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, add_r8_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

attribute [x86_compose] addR8R8Effect

theorem add_r15b_bl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x00, 0xdf])
      (addR8R8Effect p 15 3) :=
  add_r8_r8_rex_effect_step p 0x41 0xdf (by unfold RexPrefix; decide +kernel) rfl

end P256.Proofs.Common.Instructions.ByteLogic
