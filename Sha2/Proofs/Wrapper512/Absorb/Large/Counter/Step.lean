import X86Proofs.Step.MemOperand
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Instructions.Xor.Generated.M8R8.Step
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Step
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Step
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter.Decode
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter.Form

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Counter

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_m64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 64)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 8) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (addSpec
        ((Operand.mem addr : Operand 64).read t) (imm.toBitVec.signExtend 64)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm])).length =
      pre.length + 3 + am.tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_83_add_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x83 0 am hv [imm] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = imm := by
    have : (pre ++ 0x83 :: am.modrm 0 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]? =
        some imm := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [add_m64_imm8_form _ _ u _ _ _ _ hsize haddr _ _ _ _ _ _ hea hfetch hrip (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x83 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)


theorem adc_m64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 64)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 8) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeRmwOutputs t addr (addSpec
        ((Operand.mem addr : Operand 64).read t) (BitVec.ofNat 64 (t.RFLAGS.getLsbD 0).toNat)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0])).length =
      pre.length + 3 + am.tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_83_adc_memory s h _ pre.length (am.modrm 2)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2 hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x83 2 am hv [0] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = 0 :=  by
    have : (pre ++ 0x83 :: am.modrm 2 :: (am.tail ++ [0]))[pre.length + 2 + am.tail.length]? =
        some 0 := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [adc_m64_imm8_form _ _ u _ _ _ _ hsize haddr _ _ _ _ _ hea hfetch hrip (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x83 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)


end Sha2.Proofs.Wrapper512.Absorb.Large.Counter
