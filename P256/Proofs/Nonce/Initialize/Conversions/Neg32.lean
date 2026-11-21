import P256.Proofs.Common.Memory.Copy.RegisterOps.Neg

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Neg32

open P256.Proofs.Common.Instructions
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem neg_r32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [0xf7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32)
        (-((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read t),
          (subSpec 0 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read t)).2) 0 (BitVec.add s.RIP 2#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xf7, modrm] := hcode
  have f1 : (Mem_Fetch (BitVec.add s.RIP 0#64) 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xf7, afterFetches (beforeFetch s) 2) :=
    memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0
      (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at f1
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
      (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy0_run_of_opcodeF7 _ _ s.RIP (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeF7_run_of_neg_register _ _ _ _ _ hmod hreg (hmode 3) hf f2,
    neg_r32_form _ _ _ _ (hmode 3) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xf7 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

theorem neg_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xf7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (-(dst.read t), (subSpec 0 (dst.read t)).2) 0
        (BitVec.add s.RIP 3#64))) := by
  have hd := decodeLegacy0_run_of_rex_F7_neg s h rex modrm hmod hreg hcode hlow
  have hm : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r32_form _ _ _ _ hm (hrex.operand_size s.DS) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xf7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    (hm.of_cs_lma_eq rfl rfl)

def negR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (-a).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

theorem neg_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xf7, modrm])
      (negR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xf7, modrm])
      (negR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Nonce.Initialize.Conversions.Neg32
