import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Step.PrefixScan

set_option autoImplicit false

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem test_r16_r16_form {σ : Type} [PhysicalMemory σ] (s : State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.TEST_GPRv_GPRv ip ctx reg rm).run s =
      (.ok (), writeFlagsOutputs s
        (testSpec (oracleBit s.oracle)
          ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s)
          ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 16).read s)) 1 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPRv_GPRv
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.TEST => test_operation _ 16 (by decide +kernel) _ _]

def testSiState (s : RamState) : RamState :=
  afterStep s 3 fun t => writeFlagsOutputs t
    (testSpec (oracleBit t.oracle) ((Operand.reg 6 : Operand 16).read t)
      ((Operand.reg 6 : Operand 16).read t)) 1 (BitVec.add s.RIP 3#64)

theorem test_si_si_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x66, 0x85, 0xf6]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s = some (.next (testSiState s)) := by
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x85, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hcode hlow 1
      (by simp) (by decide +kernel)
  have fmod : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok 0xf6, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2
      (by simp) (by decide +kernel)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy0_run_of_opcode85 _ _ _ (oszContext s.DS) rfl fop (hm 3)
  rw [decodeLegacy0Opcode85_run_of_register _ _ _ _ _ (by decide +kernel) (hm 4) hf fmod,
    test_r16_r16_form _ _ _ _ _ (hm 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_66_legacy0 s _ h 0x85 [0xf6]
    (legacyOpcode_of_check _ ⟨by decide +kernel, by decide +kernel⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def testSiEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3, flags := some (testFlags ((Operand.reg 6 : Operand 16).read s)) }

theorem test_si_si_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x85, 0xf6]) (testSiEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, test_si_si_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  exact ⟨rfl, by simp [testSpec, testFlags, andSpec, FlagAllows], trivial,
    by simp [testSpec, testFlags, andSpec, FlagAllows],
    by simp [testSpec, testFlags, andSpec, FlagAllows], rfl⟩

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
