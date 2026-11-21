import Sha1.Proofs.Common.Instructions.MovStore.Form
import X86Proofs.Instructions.MovStore.Step
import X86Proofs.Instructions.Mov.Generated.MR.Step

namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s (pre.length + 2 + am.tail.length))) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 2 + am.tail.length))
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x89 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp only [List.length_cons, List.length_append]; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy0_run_of_89_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ pre.length (by omega)
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      (pre ++ 0x89 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h pre 0x89 reg am hv [] _ hctx hcode2 hlow2 (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  rw [mov_m_r_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip
    _ (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _)
    (hw.of_external_eq rfl)] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x89 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem mov_m_imm32_prefix_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 4) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (pre.length + 6 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 6 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 6 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (imm.signExtend n))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      pre.length + 6 + am.tail.length := by simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC7 0 am hv (immBytes 32 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 32 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC7 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 32 / 8 = pre.length + 6 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 4#64) =
        .ok (am.addrAt s (pre.length + 6 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega]
    exact hrip
  rw [mov_m_imm32_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 6 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem mov_m64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 64)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hr := hrex.rexPrefix
  have hs := mov_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  rw [scanContext_rex _ _ hr] at hs
  exact hs

theorem mov_m32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (am.addrAt s (3 + am.tail.length)) 4) :
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 32)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hr := hrex.rexPrefix
  have hs := mov_m_r_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  rw [scanContext_rex _ _ hr] at hs
  exact hs

theorem mov_m64_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s (am.addrAt s (7 + am.tail.length)) 8) :
    X86.Machine.step s = some (.next (afterStep s (7 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (7 + am.tail.length)) : Operand 64)
        (movSpec (imm.signExtend 64)) (BitVec.add s.RIP (BitVec.ofNat 64 (7 + am.tail.length))))) := by
  have hr := hrex.rexPrefix
  have hs := mov_m_imm32_prefix_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)  am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  rw [scanContext_rex _ _ hr] at hs
  exact hs

end Sha1.Proofs.Common.Instructions.MovStore
