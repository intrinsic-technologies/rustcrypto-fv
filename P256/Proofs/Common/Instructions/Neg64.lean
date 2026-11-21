import P256.Proofs.Common.Memory.Copy.RegisterOps.Neg
import P256.Proofs.Common.Instructions.Neg.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Neg64

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem neg_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NEG_GPRv ip ctx rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (-(dst.read s), (subSpec 0 (dst.read s)).2) 0 ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.NEG_GPRv
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64, oracleSkip_zero]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.NEG => neg_operation (.inr (.inr (.inr rfl))) _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem neg_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xf7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (-(dst.read t), (subSpec 0 (dst.read t)).2) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_neg s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r64_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xf7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
      (hmode.of_cs_lma_eq rfl rfl)

def negR64Effect (p : BitVec 64) (r : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg r : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg r : Operand 64), -a⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

theorem neg_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xf7, modrm])
      (negR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
      (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_rsi_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x48, 0xf7, 0xde])
      (negR64Effect p 6) :=
  neg_r64_effect_step p 0x48 0xde (by constructor <;> decide) rfl rfl

theorem neg_rcx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x48, 0xf7, 0xd9])
      (negR64Effect p 1) :=
  neg_r64_effect_step p 0x48 0xd9 (by constructor <;> decide) rfl rfl

end P256.Proofs.Common.Instructions.Neg64
