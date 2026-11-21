import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Common.EffectCompose.Conditions

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Setb (decodeLegacy1Opcode92_run_of_register setb_r_form setccR8Effect setccValue)
open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_opcode95 [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x95, t)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_92 ip context 0x95).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem setne_r8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hlowReg : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0f, 0x95, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8)
        (setccValue 5 t) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy1_run_of_opcode95 _ _ _ (legacyContext s.DS) rfl (hmode 3) fop
  rw [decodeLegacy1Opcode92_run_of_register _ _ _ _ _ _ hmod (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  change (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
      (afterFetches (beforeFetch s) 2) =
    some ((X86.Instructions.SETB_GPR8 (BitVec.add s.RIP 3#64) (legacyContext s.DS)
      (modrmRm modrm) 0x95).run (afterFetches (beforeFetch s) 4)) at hd
  rw [setb_r_form (afterFetches (beforeFetch s) 4) _ (legacyContext s.DS)
      (modrmRm modrm) 0x95 (hmode 4) rfl (.inr hlowReg)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x95 [modrm] (by decide) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem setne_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hlowReg : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0x95, modrm])
      (setccR8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) 5) := by
  rintro s h hcode rfl
  refine ⟨_, setne_r8_step s h modrm hmod hlowReg hcode.bytesAt
      (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [writeResult, Operand.write, Operand.read_reg64, Fin.getElem_fin,
    Vector.getElem_set_self]
  rfl

end P256.Proofs.Common.Instructions
