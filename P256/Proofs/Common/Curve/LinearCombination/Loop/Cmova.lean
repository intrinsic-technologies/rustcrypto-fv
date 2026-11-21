import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov

set_option autoImplicit false

namespace P256.Proofs.Common.Curve.LinearCombination.Loop

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions

theorem decodeLegacy1_run_of_cmovaOpcode [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hmode : In64BitMode u) (op : UInt8) (hop : op = 0x47)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_42 ip context op.toBitVec).run u) := by
  subst op <;>
    (unfold Decode_Legacy_1
     rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
     rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
     repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
     repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
     rfl)

theorem cmova_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex op modrm : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hop : op = 0x47) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, op, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst := gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)
    let src := gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg dst)
        (cmovR64R64Value (op.toBitVec.extractLsb' 0 4) dst src t) (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0f, op, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_cmovaOpcode _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS rex.toBitVec) rfl (hmode 4) op hop f1
  rw [decodeLegacy1Opcode42_run_of_register _ _ _ _ _ _ hmod (hmode 5) hf f2,
    cmov_r64_r64_form _ _ _ _ _ _ (hmode 5) (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex op [modrm] hrex.rexPrefix
    (by subst op <;> decide) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

theorem cmova_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex op modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : op = 0x47)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, op, modrm])
      (cmovR64R64Effect p (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmova_r64_r64_step s h rex op modrm hrex hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self]
  simp only [cmovR64R64Value, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl


end P256.Proofs.Common.Curve.LinearCombination.Loop
