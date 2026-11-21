import P256.Proofs.Common.Field.Operations.Select.TestAl
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace P256.Proofs.EcdsaSign.Core.Prepare.Candidate.Select

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Field

theorem test_cl_cl_form (s : RamState) (ip : BitVec 64) (seg : Segment)
    (hmode : In64BitMode s) :
    (X86.Instructions.TEST_GPR8_GPR8 ip (legacyContext seg) 1 1).run s =
      (.ok (), writeFlagsOutputs s
        (testSpec (oracleBit s.oracle) ((Operand.reg 1 : Operand 8).read s)
          ((Operand.reg 1 : Operand 8).read s)) 1 ip) := by
  unfold X86.Instructions.TEST_GPR8_GPR8
  simp only [legacyContext, Operand.read, writeFlagsOutputs]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ hmode,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

def testClState (s : RamState) : RamState :=
  afterStep s 2 fun t => writeFlagsOutputs t
    (testSpec (oracleBit t.oracle) ((Operand.reg 1 : Operand 8).read t)
      ((Operand.reg 1 : Operand 8).read t)) 1 (BitVec.add s.RIP 2#64)

theorem test_cl_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x84, 0xc9]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (testClState s)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x84, 0xc9] := hcode
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x84, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fmod : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run
      (afterFetches (beforeFetch s) 2) =
      (.ok 0xc9, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
      (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode84 _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode84_run_of_register _ _ _ _ _ (by decide) (hmode 3) hfeatures fmod,
    show (0xc9 : BitVec 8).extractLsb' 3 3 = 1 from rfl,
    show (0xc9 : BitVec 8).extractLsb' 0 3 = 1 from rfl,
    test_cl_cl_form _ _ _ (hmode 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x84 [0xc9]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

def testClEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2, flags := some (testFlags ((Operand.reg 1 : Operand 8).read s)) }

theorem test_cl_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x84, 0xc9]) (testClEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, test_cl_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 1 _⟩⟩
  exact ⟨rfl, by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], trivial,
    by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], rfl⟩


theorem test_cl_local (p : BitVec 64) : Effect.Local (testClEffect p) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_, fun t => ?_⟩
  · simp [testClEffect]
  · simp [testClEffect]
  · simp [testClEffect]
  · cases i <;> simp [testClEffect, testFlags, Effect.flag, StatusFlagsOutcome.get, h.read_reg]
  · simp [testClEffect]

end P256.Proofs.EcdsaSign.Core.Prepare.Candidate.Select
