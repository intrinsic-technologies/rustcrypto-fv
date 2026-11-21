import P256.Proofs.Keygen.Multiply.Projective.Lookup.Instructions.Sub
import P256.Proofs.Common.Instructions.ByteLogic.Core

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
open P256.Proofs.Common.Instructions.Setb

theorem sub_dl_cl_form (s : RamState) (ip : BitVec 64) (hmode : In64BitMode s) :
    (X86.Instructions.SUB_GPR8_GPR8_28 ip (legacyContext s.DS) 1 2).run s =
      (.ok (), writeOutputs s (.reg 2 : Operand 8)
        (subSpec ((Operand.reg 2 : Operand 8).read s) ((Operand.reg 1 : Operand 8).read s)) 0 ip) := by
  unfold X86.Instructions.SUB_GPR8_GPR8_28
  simp only [Operand.read, writeOutputs, Operand.write, legacyContext]
  spec_run [Read_GPR8 => readGPR8_run_of_low _ _ (by decide) _ hmode,
    X86.Instructions.Operations.SUB => sub_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ (by decide) _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem sub_dl_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x28,0xca]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 2 : Operand 8)
        (subSpec ((Operand.reg 2 : Operand 8).read t) ((Operand.reg 1 : Operand 8).read t)) 0
        (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcode28 _ _ _ (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode28_run_of_register _ _ _ _ _ (by decide) (hmode 3) hf fmod] at hd
  change (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
    some ((X86.Instructions.SUB_GPR8_GPR8_28 (s.RIP+2)
      (legacyContext (afterFetches (beforeFetch s) 3).DS) 1 2).run
      (afterFetches (beforeFetch s) 3)) at hd
  rw [sub_dl_cl_form _ _ (hmode 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x28 [0xca]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

def subDlClEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p+2
    writes := [⟨(Operand.reg 2 : Operand 64), mergeGPR 8
      ((Operand.reg 2 : Operand 8).read s - (Operand.reg 1 : Operand 8).read s)
      ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec ((Operand.reg 2 : Operand 8).read s)
      ((Operand.reg 1 : Operand 8).read s)).2) }

theorem sub_dl_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x28,0xca]) (subDlClEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, sub_dl_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, subSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Instructions
