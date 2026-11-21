import P256.Proofs.Common.Instructions.Setb.Decode
import P256.Proofs.Common.Instructions.Setb.Form

namespace P256.Proofs.Common.Instructions.Setb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem setcc_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex opcode modrm : UInt8) (hrex : RexPrefix rex.toBitVec)
    (hop : SupportedOpcode opcode) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, opcode, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) t) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_setcc s h (rexContext s.DS rex.toBitVec) rfl
    modrm opcode hop hmod _ 2 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [setb_r_form _ _ _ _ _ hmode rfl (.inl rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex opcode [modrm] hrex
    (by rcases hop with rfl | rfl <;> decide) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem setcc_r8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (opcode modrm : UInt8) (hop : SupportedOpcode opcode) (hmod : modrmMod modrm = 3)
    (hlowReg : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0F, opcode, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) t) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_setcc s h (legacyContext s.DS) rfl
    modrm opcode hop hmod _ 1 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [setb_r_form (afterFetches (beforeFetch s) 4)
    (BitVec.add s.RIP 3#64) (legacyContext s.DS) (modrmRm modrm) opcode.toBitVec
    hmode rfl (.inr hlowReg)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h opcode [modrm]
    (by rcases hop with rfl | rfl <;> decide) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

end P256.Proofs.Common.Instructions.Setb
