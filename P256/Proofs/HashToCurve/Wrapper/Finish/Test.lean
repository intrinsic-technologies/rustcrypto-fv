import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Test
import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

namespace P256.Proofs.HashToCurve.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions

theorem test_low8_low8_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsrc : (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hdst : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.TEST_GPR8_GPR8 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeFlagsOutputs s (testSpec (oracleBit s.oracle) (dst.read s) (src.read s)) 1 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPR8_GPR8
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [Read_GPR8 => (by first | exact readGPR8_run_of_low _ _ hdst _ hmode | exact readGPR8_run_of_low _ _ hsrc _ hmode),
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

theorem test_al_dl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x84, 0xd0]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle)
        ((Operand.reg 0 : Operand 8).read t) ((Operand.reg 2 : Operand 8).read t)) 1
        (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcode84 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0Opcode84_run_of_register _ _ _ _ _ rfl (hm 3) hf fmod,
    test_low8_low8_form _ _ _ _ _ (hm 3) (by change 2 < 4; decide) (by change 0 < 4; decide) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x84 [0xd0]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hm 3).of_cs_lma_eq rfl rfl)

def testAlDlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2
    flags := some (testFlags ((Operand.reg 0 : Operand 8).read s &&&
      (Operand.reg 2 : Operand 8).read s)) }

theorem test_al_dl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x84, 0xd0]) (testAlDlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, test_al_dl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 1 _⟩⟩
  exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

end P256.Proofs.HashToCurve.Wrapper.Finish
