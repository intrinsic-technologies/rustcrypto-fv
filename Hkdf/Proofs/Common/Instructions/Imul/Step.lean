import Hkdf.Proofs.Common.Instructions.Imul.Decode
import Hkdf.Proofs.Common.Instructions.Imul.Form

set_option autoImplicit false

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem imul_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xAF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (imulSpec64 t.oracle (dst.read t) (src.read t))
        4 (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_imul_register s h (rexContext s.DS rex.toBitVec) rfl
    modrm hmod _ 2 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r64_r64_form _ _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xAF [modrm] hrex.rexPrefix (by decide)
    hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

end Hkdf.Proofs.Common.Instructions
