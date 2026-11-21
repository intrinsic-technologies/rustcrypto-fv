import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleDecode
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleForm

namespace P256.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shld_r64_r64_one_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xA4, modrm, 1])
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      writeOutputs t dst (shldOneSpec (oracleBit t.oracle) (dst.read t) (src.read t))
        1 (BitVec.add s.RIP 5#64))) := by
  have hdecode := decodeLegacy1_run_of_shld s h (rexContext s.DS rex.toBitVec) rfl
    modrm hmod _ 2 (by decide) rfl rfl hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 4#64) 8).run (afterFetches (beforeFetch s) 5) =
      (.ok 1, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt (beforeFetch s) 5 h.fetchReady hcode hlow 4 (by simp) (by decide)
  rw [shld_r64_r64_one_form _ _ _ _ _ _ (hmode 5) himm (hmode 6)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 4#64) 1#64 = BitVec.add s.RIP 5#64 from
      BitVec.add_assoc s.RIP 4#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xA4 [modrm, 1] hrex.rexPrefix (by decide)
    hcode hlow hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

end P256.Proofs.Common.Instructions.ShiftLeft
