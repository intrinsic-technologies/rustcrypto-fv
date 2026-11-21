import X86Proofs.Program.ReadWrite.LoadFlags
import X86Proofs.Instructions.MovLoad.Step
import P256.Proofs.Common.Instructions.Imul.Memory.Decode
import P256.Proofs.Common.Instructions.Imul.Memory.Form

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem imul_r64_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: 0xAF :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (4 + am.tail.length)) 8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeOutputs (dataAccess t "load") dst
        (imulSpec64 (oracleSkip t.oracle 464) (dst.read t)
          ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 64).read t)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x0F :: 0xAF :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy1_run_of_imul_memory s h (rexContext s.DS rex.toBitVec) rfl
    (am.modrm reg) (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    _ 2 (by decide) rfl rfl hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x0F :: 0xAF :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 5 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 4
    (fun j _ => by rw [show 4 + j = j + 1 + 1 + 1 + 1 by omega]; rfl) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 5 + am.tail.length = 4 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 4#64)).run (afterFetches (beforeFetch s) 5) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (4 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (4 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))) =
      am.addrAt s (4 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)))
  rw [haddr] at hrip
  rw [imul_r64_m64_form _ t _ _ _ _ _ (hrex.operand_size s.DS) rfl rfl _ _ _ _ _ hea hrip ht hmode hread.low
    hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xAF _ hrex.rexPrefix (by decide)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end P256.Proofs.Common.Instructions
