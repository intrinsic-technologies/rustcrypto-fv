import X86Proofs.Instructions.Rol.Generated.R.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_66_C1_rol [Bindings] (s : RamState) (h : ReadyToStep s) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP [0x66, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.ROL_GPRv_IMMb (BitVec.add s.RIP 3#64)
        (oszContext s.DS) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x66, 0xC1, modrm, imm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xC1, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeC1 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeC1_run_of_rol_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl


theorem rol_r16_imm8_form [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 16 count
      (.ok (), writeOutputs t dst (rolSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read s)) (rolOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ROL_GPRv_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ROL => rol_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem rol_r16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP [0x66, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 16 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (rolSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read t))
        (rolOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_66_C1_rol s h modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [rol_r16_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0xC1 [modrm, imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)


def rolR16Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (((Operand.reg dst : Operand 16).read s).rotateLeft 8)
        ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem rol_r16_eight_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0xc1, modrm, 8])
      (rolR16Effect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, rol_r16_imm8_step s h modrm 8 hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, setFlags, Operand.read, Operand.write, rolSpec,
      afterFetches, beforeFetch, resetStepFields, shiftCount]
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

@[x86_local] theorem rolR16Effect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (rolR16Effect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [rolR16Effect, h.read_reg]
  · intro s
    simp [rolR16Effect, Write.Full, Operand.Full]

attribute [x86_compose] rolR16Effect

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
