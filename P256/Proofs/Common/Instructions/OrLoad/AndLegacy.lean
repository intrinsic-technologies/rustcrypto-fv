import P256.Proofs.Common.Instructions.ByteLogic.AndReg

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteLogic (decodeLegacy0Opcode20_run_of_register)
open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem and_r8_r8_low_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsrc : (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hdst : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.AND_GPR8_GPR8_20 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (andSpec (oracleBit s.oracle) (dst.read s) (src.read s)) 1 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.AND_GPR8_GPR8_20
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by first | exact hsrc | exact hdst) _ hmode,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ hdst _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0_run_of_20_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x20, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.AND_GPR8_GPR8_20 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x20, modrm] := hcode
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x20, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fmod : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [X86Proofs.decodeLegacy0_run_of_opcode20 _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2),
    decodeLegacy0Opcode20_run_of_register _ _ s.RIP _ _ hmod (hmode 3) hf fmod]
  rfl

theorem and_r8_r8_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4)
    (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x20, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 0 (modrmReg modrm))
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (src.read t)) 1
        (BitVec.add s.RIP 2#64))) := by
  have hd := decodeLegacy0_run_of_20_register s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hform := and_r8_r8_low_form (afterFetches (beforeFetch s) 3)
    (BitVec.add s.RIP 2#64) (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm)
    hmode hsrc hdst rfl
  have hd' := hd.trans (congrArg some hform)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x20 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd'
    (hmode.of_cs_lma_eq rfl rfl)

def andR8R8LegacyEffect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s &&& (Operand.reg src : Operand 8).read s
  { rip := p + 2
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (andFlags r) }

theorem and_r8_r8_legacy_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4)
    (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x20, modrm])
      (andR8R8LegacyEffect p (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, and_r8_r8_legacy_step s h modrm hmod hsrc hdst hcode.bytesAt
      (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, andSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] andR8R8LegacyEffect

end P256.Proofs.Common.Instructions
