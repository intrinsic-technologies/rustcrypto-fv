import P256.Proofs.Common.Instructions.AddByte.Effect
import P256.Proofs.Common.Instructions.ByteLogic.Core
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_r8_imm8_low_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hsmall : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t))
    (htmode : In64BitMode t) :
    (X86.Instructions.ADD_GPR8_IMMb_80r0 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (addSpec (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_GPR8_IMMb_80r0
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ hsmall _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => X86Proofs.writeGPR8_run_of_low _ _ hsmall _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem add_r8_imm8_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 0) (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (addSpec (dst.read t) (imm.signExtend 8)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by simpa using hlow
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x80, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fmod : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow' 1 (by simp) (by decide)
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 8 (by decide) imm 2
    (immBytes_getElem?_append [0x80,modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    h.features.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have hd := decodeLegacy0_run_of_opcode80 _ _ _ (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode80_run_of_r0_register _ _ _ _ _ hmod hreg (hmode 3) hf fmod] at hd
  change (Decode_Legacy_0 _ _).run _ = some ((X86.Instructions.ADD_GPR8_IMMb_80r0 _ _ (modrmRm modrm)).run _) at hd
  rw [add_r8_imm8_low_form _ _ (BitVec.add s.RIP 2#64) (legacyContext s.DS) (modrmRm modrm) imm
    (hmode 3) hsmall rfl himm (hmode 4),
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x80 _ (legacyOpcode_of_check _ ⟨by decide,by decide⟩)
    hcode hlow' hd ((hmode 4).of_cs_lma_eq rfl rfl)

def addR8Imm8LegacyEffect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  { addR8Imm8Effect p dst imm s with rip := p + 3 }

theorem add_r8_imm8_legacy_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (addR8Imm8LegacyEffect p (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_r8_imm8_legacy_step s h modrm imm hmod hreg hsmall hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · simpa only [Operand.read_afterFetches, Operand.read_beforeFetch, BitVec.signExtend_eq] using
      StatusFlagsOutcome.allows_ofStatusFlags (addSpec
        ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read s) imm).2

@[x86_local] theorem addR8Imm8LegacyEffect_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (addR8Imm8LegacyEffect p dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [addR8Imm8LegacyEffect, addR8Imm8Effect, h.read_reg]
  · intro s
    simp [addR8Imm8LegacyEffect, addR8Imm8Effect, Write.Full, Operand.Full]

attribute [x86_compose] addR8Imm8LegacyEffect addR8Imm8Effect

theorem add_cl_ff_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x80, 0xc1, 0xff])
      (addR8Imm8LegacyEffect p 1 0xff) :=
  add_r8_imm8_legacy_effect_step p 0xc1 0xff rfl rfl (by decide)

end P256.Proofs.Common.Instructions.AddByte
