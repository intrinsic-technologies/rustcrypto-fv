import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions
import P256.Proofs.Common.EffectCompose
import X86Proofs.Instructions.Sub.Operation

set_option autoImplicit false

namespace P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem sub_r8_r8_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SUB_GPR8_GPR8_28 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (subSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SUB_GPR8_GPR8_28
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.SUB => sub_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0Opcode28_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_28 ip ctx).run s =
      (X86.Instructions.SUB_GPR8_GPR8_28 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_28 ctx true a b c d e f modrm = .ok 1 := by
    simp [Select_Legacy_0_Opcode_28, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_28
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem sub_r8_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex,0x28,modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (subSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode28 _ _ _ (rexContext s.DS rex.toBitVec) rfl fop (hmode 3)
  rw [decodeLegacy0Opcode28_run_of_register _ _ _ _ _ hmod (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, sub_r8_r8_form _ _ _ _ _ (hmode 4) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x28 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def subR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s - (Operand.reg src : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec ((Operand.reg dst : Operand 8).read s) ((Operand.reg src : Operand 8).read s)).2) }

theorem sub_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex,0x28,modrm])
      (subR8R8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r8_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, subSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

@[x86_local] theorem subR8R8Effect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (subR8R8Effect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [subR8R8Effect, h.read_reg]
  · intro s
    simp [subR8R8Effect, Write.Full, Operand.Full]

@[simp] theorem subR8R8Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (subR8R8Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

attribute [x86_compose] subR8R8Effect

end P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
