import P256.Proofs.Common.Instructions.NegByte
import P256.Proofs.Common.Instructions.ByteLogic.AndReg

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions.NegByte

theorem neg_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xf6, 0xd8]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 0 : Operand 8)
        (-((Operand.reg 0 : Operand 8).read t), (subSpec 0 ((Operand.reg 0 : Operand 8).read t)).2)
        0 (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeF6 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeF6_run_of_neg_register _ _ _ _ _ rfl rfl (hm 3) hf fmod,
    neg_r8_form _ _ _ _ (hm 3) rfl (.inr (by change (0 : Nat) < 4; decide))] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xf6 [0xd8]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hm 3).of_cs_lma_eq rfl rfl)

def negAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (-((Operand.reg 0 : Operand 8).read s)) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec 0 ((Operand.reg 0 : Operand 8).read s)).2) }

theorem neg_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xf6, 0xd8]) (negAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, neg_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, subSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

attribute [x86_compose] negAlEffect

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions
