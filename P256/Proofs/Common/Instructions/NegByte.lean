import X86Proofs.Instructions.Sub.Operation
import P256.Proofs.Common.Instructions.ByteLogic.Core
import P256.Proofs.Common.EffectCompose
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.Decode.Legacy0

import P256.Proofs.Common.Instructions.Neg.Operation

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteLogic (readGPR8_run writeGPR8_run)

namespace P256.Proofs.Common.Instructions.NegByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

open scoped X86.Runtime.Syntax

theorem neg_r8_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.NEG_GPR8 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (-(dst.read s), (subSpec 0 (dst.read s)).2) 0 ip) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hctx]
  unfold X86.Instructions.NEG_GPR8
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    X86.Instructions.Operations.NEG => neg_operation (.inl rfl) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0OpcodeF6_run_of_neg_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_F6 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_F6, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0OpcodeF6_run_of_neg_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F6 ip context).run s =
      (X86.Instructions.NEG_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F6
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeF6_run_of_neg_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_F6_neg [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xF6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.NEG_GPR8 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0xF6, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xF6, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeF6 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeF6_run_of_neg_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem neg_r8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xf6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (-(dst.read t), (subSpec 0 (dst.read t)).2) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F6_neg s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r8_form _ _ _ _ hmode rfl (.inl rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xf6 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
      (hmode.of_cs_lma_eq rfl rfl)

def negR8Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (-a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

theorem neg_r8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xf6, modrm])
      (negR8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r8_step s h rex modrm hrex hmod hreg hcode.bytesAt
      (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, subSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r14b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41,0xf6,0xde])
      (negR8Effect p 14) :=
  neg_r8_effect_step p 0x41 0xde (by unfold RexPrefix; decide) rfl rfl

attribute [x86_compose] negR8Effect

end P256.Proofs.Common.Instructions.NegByte
