import P256.Proofs.Common.Instructions.NegByte
import P256.Proofs.Common.Instructions.OrLoad.AndLegacy

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.NegByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem neg_r8_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (haccess : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0xf6, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (-(dst.read t), (subSpec 0 (dst.read t)).2) 0
        (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeF6 _ _ s.RIP (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeF6_run_of_neg_register _ _ _ _ _ hmod hreg (hm 3) hf fmod] at hd
  have form := neg_r8_form (afterFetches (beforeFetch s) 3) (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) (modrmRm modrm) (hm 3) rfl (Or.inr haccess)
  erw [form] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xf6 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hm 3).of_cs_lma_eq rfl rfl)

def negR8LegacyEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { negR8Effect p dst s with rip := p + 2 }

theorem neg_r8_legacy_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (haccess : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xf6, modrm])
      (negR8LegacyEffect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r8_legacy_step s h modrm hmod hreg haccess hcode.bytesAt
      (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write,
      subSpec, setFlags, afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Instructions.NegByte
