import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions

set_option autoImplicit false

namespace P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem cmp_r8_imm8_rex_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.CMP_GPR8_IMMb_80r7 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeFlagsOutputs t (cmpSpec (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPR8_IMMb_80r7
  simp only [Operand.read, writeFlagsOutputs, oracleSkip_zero, hrex]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

theorem decode80_cmp_dil [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xff, t)) :
    (Decode_Legacy_0_Opcode_80 ip ctx).run s =
      (X86.Instructions.CMP_GPR8_IMMb_80r7 (BitVec.add ip 2#64) ctx 7).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_80 ctx true a b c d e f 0xff = .ok 16 := rfl
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem cmp_dil_seven_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x40, 0x80, 0xff, 7]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 4 fun t => writeFlagsOutputs t
      (cmpSpec ((Operand.reg 7 : Operand 8).read t) 7) 0 (BitVec.add s.RIP 4#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have fimm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok 7, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  have hd := decodeLegacy0_run_of_opcode80 _ _ _ (rexContext s.DS 0x40) rfl fop (hmode 3)
  rw [decode80_cmp_dil _ _ _ _ (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from BitVec.add_assoc _ _ _,
    cmp_r8_imm8_rex_form _ _ _ _ _ _ (hmode 4) rfl rfl fimm,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x40 0x80 [0xff, 7] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

def cmpDilSevenEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 7 : Operand 8).read s) 7)) }

theorem cmp_dil_seven_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x40, 0x80, 0xff, 7])
      (cmpDilSevenEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_dil_seven_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 0 _, ?_⟩
  refine ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Curve.LinearCombination.Loop.Instructions
