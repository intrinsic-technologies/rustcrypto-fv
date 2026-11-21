import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import X86Proofs.Step.Decode.Legacy0Opcode81

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_81_r4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (0x81 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.AND_GPRv_IMMz (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x81 :: modrm :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x81 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x81, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode81 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode81_run_of_r4_register _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

theorem and_r_imm32_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 32) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.AND_GPRv_IMMz ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend n)) 1
        (BitVec.add ip 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.AND_GPRv_IMMz
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.AND => and_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.AND_GPRv_IMMz
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.AND => and_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem and_r32_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (0x81 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 6 fun t ↦
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 32)) 1
        (BitVec.add s.RIP 6#64))) := by
  have hdecode := decodeLegacy0_run_of_81_r4 s h modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x81 :: modrm :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x81 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 32 (by decide) imm 2
    (immBytes_getElem?_append [0x81, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [and_r_imm32_form _ _ (BitVec.add s.RIP 2#64) _ _ imm (hmode 3) 32 (by decide)
    (legacyContext_operand_size s.DS) rfl himm (hmode 7),
    show BitVec.add (BitVec.add s.RIP 2#64) 4#64 = BitVec.add s.RIP 6#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x81 (modrm :: immBytes 32 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 7).of_cs_lma_eq rfl rfl)

theorem and_r32_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 6 fun t ↦
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 32)) 1
        (BitVec.add s.RIP 6#64)) :=
  ReadyToStep.afterStep_writeOutputs h 6 _ _ 1 _

def andR32Imm32Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 32).read s &&& imm
  { rip := p + 6
    writes := [⟨(Operand.reg dst : Operand 64), r.setWidth 64⟩]
    flags := some (andFlags r) }

theorem and_r32_imm32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (andR32Imm32Effect p (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r32_imm32_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_r32_imm32_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, BitVec.signExtend_eq]
  · simp only [BitVec.signExtend_eq]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_ecx_fc_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x81, 0xE1, 0xFC, 0, 0, 0])
      (andR32Imm32Effect p 1 0xFC) :=
  and_r32_imm32_effect_step p 0xE1 0xFC (by decide) (by decide)

end X86Proofs
