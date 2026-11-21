import Md5.Proofs.Buffered.Stores.Form
import X86Proofs.Instructions.MovStore.Step

namespace Md5.Proofs.Buffered.Stores

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem mov_rex_89_memory_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (rexContext s.DS rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) (n / 8)) :
    let src : Operand n := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand n)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (rex :: 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_pfx_89_memory s h rex (am.modrm reg) (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x89 :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ => getElem?_cons3 _ _ _ _ j) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
      am.addrAt s (3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_m_r_form _ t _ _ _ _ _ n hn hsize rfl rfl _ _ _ _ _ hea hrip ht hmode
    (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x89 _ hrex (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 64)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step s h rex hrex.rexPrefix 64 (.inl rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

theorem mov_m32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 4) :
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 32)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step s h rex hrex.rexPrefix 32 (.inr rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

theorem mov_m64_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (7 + am.tail.length)) 8) :
    X86.Machine.step s = some (.next (afterStep s (7 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (7 + am.tail.length)) : Operand 64)
        (movSpec (imm.signExtend 64)) (BitVec.add s.RIP (BitVec.ofNat 64 (7 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_pfx_C7_memory s h rex (am.modrm 0) (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j hj => getElem?_cons3_append _ _ _ _ _ j hj) (by simp; omega) (by omega)
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (4 + am.tail.length)) := hea
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (4 + am.tail.length) h.fetchReady hc hlow' 32
    (by decide) imm (3 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (rex :: 0xC7 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + 1 + j = 3 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 4 + am.tail.length + 32 / 8 = 7 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (7 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 4#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (7 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (3 + am.tail.length) 4
    rw [show 3 + am.tail.length + 4 = 7 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 4#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (7 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  rw [mov_m_imm32_form _ _ u _ _ _ _ 64 (.inl rfl) (hrex.operand_size s.DS) rfl rfl _ _ _ _ _ imm
    hea himm hrip hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC7 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_C6_memory s h (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j hj => getElem?_cons2_append _ _ _ _ j hj) (by simp; omega) (by omega)
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (3 + am.tail.length) h.fetchReady hc hlow' 8
    (by decide) imm (2 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (0xC6 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + j = 2 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 3 + am.tail.length + 8 / 8 = 3 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (2 + am.tail.length) 1
    rw [show 2 + am.tail.length + 1 = 3 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 1#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (3 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  have hea' : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length)) := hea
  rw [mov_m8_imm8_form _ _ u _ _ _ _ rfl rfl _ _ _ _ _ imm hea' himm hrip hu
    (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC6 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode
    hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end Md5.Proofs.Buffered.Stores
