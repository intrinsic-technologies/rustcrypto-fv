import P256.Proofs.Program.Compare.Instructions.ByteRegister
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple

namespace P256.Proofs.Program.Compare.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem test_r8_imm8_low_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8)
    (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (hreg : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.TEST_GPR8_IMMb_F6r0 ip ctx rm).run s =
      (.ok (), writeFlagsOutputs t (testSpec (oracleBit t.oracle)
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 8).read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hreg ⊢
  unfold X86.Instructions.TEST_GPR8_IMMb_F6r0
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex_or_low _ _ _ hmode (.inr hreg),
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide +kernel) _ _]

theorem test_r8_imm8_low_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hlowReg : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (0xF6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeFlagsOutputs t (testSpec (oracleBit t.oracle)
        ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read t) imm) 1
        (BitVec.add s.RIP 3#64))) := by
  have hlow' : s.RIP.toNat + (0xF6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have hd := decodeLegacy0_run_of_modrm_at s h
    (0xF6 :: modrm :: immBytes 8 imm) 0 0xF6 modrm hcode hlow' rfl rfl
    (by decide +kernel) (legacyContext s.DS) _ _
    (fun a u hf hm ↦ decodeLegacy0_run_of_opcodeF6 a u _ _ rfl hf hm)
    (fun a u hf hm hfe ↦
      decodeLegacy0OpcodeF6_run_of_r0_register a u _ _ _ hmod hreg hm hfe hf)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at hd
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0xF6 :: modrm :: immBytes 8 imm) := hcode
  have hi := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow'
    8 (by decide +kernel) imm 2 (immBytes_getElem?_append [0xF6, modrm] imm)
    (by simp) (by decide +kernel)
  have hm : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf := test_r8_imm8_low_form (afterFetches (beforeFetch s) 3)
    (afterFetches (beforeFetch s) 4) (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) (modrmRm modrm) imm hm rfl hlowReg hi
  rw [BitVec.signExtend_eq,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hf
  have hd' := hd.trans (congrArg some hf)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF6 (modrm :: immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide +kernel, by decide +kernel⟩)
    hcode hlow' hd' (hm.of_cs_lma_eq rfl rfl)

end P256.Proofs.Program.Compare.Instructions
