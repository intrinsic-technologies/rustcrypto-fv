import Md5.Proofs.Buffered.Update.Counter.Decode
import Md5.Proofs.Buffered.Update.Counter.Form
import X86Proofs.Step.MemOperand
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Instructions.Xor.Generated.M8R8.Step
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Step
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Step
import X86Proofs.Instructions.MovLoad.Step

namespace Md5.Proofs.Buffered.Update.Counter

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem inc_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t ↦
      writeRmwOutputs t (am.addrAt s (3 + am.tail.length))
        (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hlow' : s.RIP.toNat + (rex :: 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]
    omega
  have hdecode := decodeLegacy0_run_of_rex_FF_inc_memory s h rex (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (by rw [AddrMode.modrmReg_modrm]) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0xFF :: am.modrm 0 :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ ↦ getElem?_cons3 _ _ _ _ j) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [inc_m64_form _ t _ _ _ _ (hrex.operand_size s.DS) rfl _ _ _ _ _ hea hrip
    (memAlu_dataReady h _) (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xFF _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem add_m64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x01 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t ↦
      writeRmwOutputs t (am.addrAt s (3 + am.tail.length))
        (addSpec ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t)
          (src.read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (rex :: 0x01 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]
    omega
  have hdecode := decodeLegacy0_run_of_rex_01_add_memory s h rex (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0x01 :: am.modrm reg :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ ↦ getElem?_cons3 _ _ _ _ j) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [add_m64_r64_form _ t _ _ _ _ _ (hrex.operand_size s.DS) rfl _ _ _ _ _ hea hrip
    (memAlu_dataReady h _) hmode (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x01 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end Md5.Proofs.Buffered.Update.Counter
