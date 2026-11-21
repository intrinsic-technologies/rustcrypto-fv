import Sha2.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m_r_form_any [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : Writable t addr (n / 8)) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (src.read t))
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_any _ (ht.withNextIP next) isStack addr 64 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_any _ (ht.withNextIP next) isStack addr 32 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

theorem mov_rex_89_memory_step_any [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (rexContext s.DS rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (3 + am.tail.length)) (n / 8)) :
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
  rw [mov_m_r_form_any _ t _ _ _ _ _ n hn hsize rfl rfl _ _ _ _ _ hea hrip ht hmode
    (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x89 _ hrex (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m64_r64_step_any [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 64)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step_any s h rex hrex.rexPrefix 64 (.inl rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

theorem mov_m32_r32_step_any [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (3 + am.tail.length)) 4) :
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 32)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step_any s h rex hrex.rexPrefix 32 (.inr rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

theorem mov_m64_r64_effect_step_any [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Pre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  effect_step_of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_r64_step_any s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m32_r32_effect_step_any [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Pre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  effect_step_of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_step_any s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Sha2.Proofs.Common.Instructions.CrossPageStore
