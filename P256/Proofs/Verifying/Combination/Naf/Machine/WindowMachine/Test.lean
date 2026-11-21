import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem test_dl_one_form [Bindings] (s t : RamState) (ip : BitVec 64) (seg : Segment)
    (mode : In64BitMode s) (fetch : (Mem_Fetch ip 8).run s = (.ok 1, t)) :
    (X86.Instructions.TEST_GPR8_IMMb_F6r0 ip (legacyContext seg) 2).run s =
      (.ok (), writeFlagsOutputs t
        (testSpec (oracleBit t.oracle) ((Operand.reg 2 : Operand 8).read s) 1) 1 (ip + 1)) := by
  unfold X86.Instructions.TEST_GPR8_IMMb_F6r0
  simp only [legacyContext, Operand.read, writeFlagsOutputs]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ mode,
    Mem_Fetch => fetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

def testDlOneState (s : RamState) : RamState :=
  afterStep s 3 fun t => writeFlagsOutputs t
    (testSpec (oracleBit t.oracle) ((Operand.reg 2 : Operand 8).read t) 1) 1 (BitVec.add s.RIP 3#64)

set_option maxHeartbeats 500000 in
theorem test_dl_one_step [Bindings] (s : RamState) (ready : ReadyToStep s)
    (code : BytesAt s s.RIP [0xf6, 0xc2, 1]) (low : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s = some (.next (testDlOneState s)) := by
  have bytes : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xf6, 0xc2, 1] := code
  have opcode : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xf6, afterFetches (beforeFetch s) 2) := by
    have fetch := memFetch_run_of_bytesAt (beforeFetch s) 1 ready.fetchReady bytes low 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at fetch
  have modrm : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xc2, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 ready.fetchReady bytes low 1
      (by simp) (by decide)
  have immediate : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 1, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 ready.fetchReady bytes low 2
      (by simp) (by decide)
  have mode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment ready.cpu.cs ready.cpu.efer.lma
  have features : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ ready.features
  have decode := decodeLegacy0_run_of_opcodeF6 _ _ s.RIP (legacyContext s.DS) rfl opcode (mode 2)
  rw [decodeLegacy0OpcodeF6_run_of_r0_register _ _ _ _ _ (by decide) (by decide)
    (mode 3) features modrm,
    show (0xc2 : BitVec 8).extractLsb' 0 3 = 2 from rfl,
    test_dl_one_form _ _ _ _ (mode 3) immediate] at decode
  rw [show BitVec.add s.RIP 2#64 + 1 = BitVec.add s.RIP 3#64 from
    BitVec.add_assoc _ _ _] at decode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact ready.ready.repeatClear
  exact step_none_legacy0 s _ ready 0xf6 [0xc2, 1]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) code low decode
    ((mode 4).of_cs_lma_eq rfl rfl)

def testDlOneEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3, flags := some (testFlags ((Operand.reg 2 : Operand 8).read s &&& 1)) }

theorem test_dl_one_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xf6, 0xc2, 1]) (testDlOneEffect p) := by
  rintro s ready code rfl
  refine ⟨_, test_dl_one_step s ready code.bytesAt (code.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs ready 3 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip ready 3 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

end P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine
