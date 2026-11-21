import X86Proofs.Step.AfterStep
import Sha3.Proofs.X86.Instructions.MemAlu.Decode
import Sha3.Proofs.X86.Instructions.MemAlu.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem getElem?_pre_op (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ op :: m :: l)[pre.length]? = some op := by simp

theorem getElem?_pre_modrm (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ op :: m :: l)[pre.length + 1]? = some m := by simp

theorem getElem?_pre_tail (pre : List UInt8) (op m : UInt8) (l : List UInt8) (j : Nat) :
    (pre ++ op :: m :: l)[pre.length + 2 + j]? = l[j]? := by
  rw [List.getElem?_append_right (by omega), show pre.length + 2 + j - pre.length = j + 1 + 1 by
    omega]
  rfl

theorem memAlu_ea [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8) (op : UInt8)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (rest : List UInt8)
    (ctx : Instruction_Context) (hctx : AddrContext ctx am)
    (hcode : BytesAt s s.RIP (pre ++ op :: am.modrm reg :: (am.tail ++ rest)))
    (hlow : s.RIP.toNat + (pre ++ op :: am.modrm reg :: (am.tail ++ rest)).length ≤ 2^32)
    (h15 : pre.length + 2 + am.tail.length ≤ 15) :
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))).run
        (afterFetches (beforeFetch s) (pre.length + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: am.modrm reg :: (am.tail ++ rest)) := hcode
  refine effectiveAddress_run (beforeFetch s) (pre.length + 3) h.fetchReady h.cpu.ds h.cpu.ss am
    hv ctx hctx hc hlow (pre.length + 2) (fun j hj => ?_) (by simp; omega) h15
  rw [getElem?_pre_tail, List.getElem?_append_left hj]

theorem memAlu_dataReady [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) :=
  h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables

theorem xor_m_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x31 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) (n / 8)) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand n).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x31 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x31 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_31_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x31 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [xor_m_r_form _ t _ _ _ _ _ n hn hsize haddr _ _ _ _ _ hea hrip (memAlu_dataReady h _) hmode
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x31 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem xor_m8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x30 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t =>
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand 8).read t) (src.read t)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x30 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x30 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_30_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x30 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [xor_m8_r8_form _ t _ _ _ _ _ haddr hreg _ _ _ _ _ hea hrip (memAlu_dataReady h _) hmode
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x30 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem add_tail_imm (r : BitVec 64) (a : Nat) :
    BitVec.add (BitVec.add r (BitVec.ofNat 64 a)) 1#64 = BitVec.add r (BitVec.ofNat 64 (a + 1)) :=
  add_ofNat_add r a 1

theorem xor_m8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 1) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (xorSpec (oracleBit (dataAccess t "load").oracle)
        ((Operand.mem addr : Operand 8).read t) (imm.toBitVec.signExtend 8)) 1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm])).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_80_r6_memory s h _ pre.length (am.modrm 6)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x80 6 am hv [imm] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = imm := by
    have : (pre ++ 0x80 :: am.modrm 6 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]? =
        some imm := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [xor_m8_imm8_form _ _ u _ _ _ _ haddr _ _ _ _ _ _ hea hfetch hrip (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x80 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_m8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 1) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem addr : Operand 8).read t) (imm.toBitVec.signExtend 8)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm])).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_80_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x80 7 am hv [imm] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = imm := by
    have : (pre ++ 0x80 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]? =
        some imm := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [cmp_m8_imm8_form _ _ u _ _ _ _ haddr hlock _ _ _ _ _ _ hea hfetch hrip
    (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x80 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
