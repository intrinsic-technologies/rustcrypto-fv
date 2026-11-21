import X86Proofs.Program.Effect
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Field

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectLegacy0Opcode84_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_84 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_84, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode84_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_84 ip context).run s =
      (X86.Instructions.TEST_GPR8_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_84
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode84_run_of_register context a b c d e f modrm hmod)

theorem test_al_al_form (s : RamState) (ip : BitVec 64) (seg : Segment)
    (hmode : In64BitMode s) :
    (X86.Instructions.TEST_GPR8_GPR8 ip (legacyContext seg) 0 0).run s =
      (.ok (), writeFlagsOutputs s
        (testSpec (oracleBit s.oracle) ((Operand.reg 0 : Operand 8).read s)
          ((Operand.reg 0 : Operand 8).read s)) 1 ip) := by
  unfold X86.Instructions.TEST_GPR8_GPR8
  simp only [legacyContext, Operand.read, writeFlagsOutputs]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ hmode,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

def testAlState (s : RamState) : RamState :=
  afterStep s 2 fun t => writeFlagsOutputs t
    (testSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read t)
      ((Operand.reg 0 : Operand 8).read t)) 1 (BitVec.add s.RIP 2#64)

theorem test_al_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x84, 0xc0]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (testAlState s)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x84, 0xc0] := hcode
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x84, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fmod : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run
      (afterFetches (beforeFetch s) 2) =
      (.ok 0xc0, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
      (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode84 _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode84_run_of_register _ _ _ _ _ (by decide) (hmode 3) hfeatures fmod,
    show (0xc0 : BitVec 8).extractLsb' 3 3 = 0 from rfl,
    show (0xc0 : BitVec 8).extractLsb' 0 3 = 0 from rfl,
    test_al_al_form _ _ _ (hmode 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x84 [0xc0]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

def testAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2, flags := some (testFlags ((Operand.reg 0 : Operand 8).read s)) }

theorem test_al_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x84, 0xc0]) (testAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, test_al_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 1 _⟩⟩
  exact ⟨rfl, by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], trivial,
    by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], by simp [testSpec, testFlags, andSpec, FlagAllows, afterFetches, beforeFetch, resetStepFields], rfl⟩

end P256.Proofs.Common.Field
