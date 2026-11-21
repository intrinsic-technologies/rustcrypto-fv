import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0Opcode80
import X86Proofs.Instructions.Or.Operation
import Hkdf.Proofs.Common.Instructions.Or

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.PreviousCopy

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

private theorem or_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hr : (ctx.rex_prefix_present || ctx.rex2_prefix_present || ctx.vex_prefix_present ||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.OR_GPR8_IMMb_80r1 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (orSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.OR_GPR8_IMMb_80r1
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ hr hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.OR => or_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ hr _ (htmode.of_cs_lma_eq rfl rfl)]


private theorem decodeLegacy0_run_of_80_r1 [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP (0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.OR_GPR8_IMMb_80r1 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x80, afterFetches (beforeFetch s) 2) := by
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
  rw [decodeLegacy0_run_of_opcode80 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode80_run_of_r1_register _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl


private theorem or_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeOutputs t dst (orSpec (oracleBit t.oracle) (dst.read t) imm) 1 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_80_r1 s h modrm imm hmod hreg hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow'
    8 (by decide) imm 2 (immBytes_getElem?_append [0x80, modrm] imm) (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hform := or_r8_imm8_form _ _ (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) (modrmRm modrm) imm (hmode 3)
    (Or.inr hr) rfl himm (hmode 4)
  rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
    BitVec.add_assoc _ _ _] at hform
  simp only [BitVec.signExtend_eq] at hform
  replace hdecode := hdecode.trans (congrArg some hform)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x80 (modrm :: immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    ((hmode 4).of_cs_lma_eq rfl rfl)


private theorem readOrResult (s : RamState) (r : BitVec 5)
    (out : BitVec 8 × StatusFlags) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read
      (writeOutputs s (.reg r : Operand 8) out 1 nextIP) =
      mergeGPR 8 out.1 ((Operand.reg r : Operand 64).read s) := by
  simp [writeOutputs, setFlags, Operand.read, Operand.write]

def orR8Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a ||| imm) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (Hkdf.Proofs.Common.Instructions.Or.orFlags (a ||| imm)) }

theorem or_r8_imm8_effect_step [Bindings] (p : BitVec 64)
    (modrm : UInt8) (imm : BitVec 8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    : StepEffect (fun s ↦ s.RIP = p)
      (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (orR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, or_r8_imm8_step s h modrm imm hmod hreg hr hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, readOrResult]
    simp only [orSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] orR8Imm8Effect

attribute [x86_compose] orR8Imm8Effect

@[x86_local] theorem orR8Imm8Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) : Effect.Local (orR8Imm8Effect p len dst imm) := by
  effect_local [orR8Imm8Effect]

end Hkdf.Proofs.NewExpand.Expand.PreviousCopy
