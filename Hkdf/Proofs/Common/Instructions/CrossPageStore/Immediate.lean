import Hkdf.Proofs.Common.Instructions.CrossPageStore.Mov

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m_imm32_form_any [Bindings] (s t u : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool)
    (imm : BitVec 32)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 32).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 4#64) = .ok addr)
    (hu : DataReady u) (hw : Writable u addr (n / 8)) :
    (X86.Instructions.MOV_MEMv_IMMz_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem addr : Operand n)
        (movSpec (imm.signExtend n)) (BitVec.add next 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_any _ (hu.withNextIP (BitVec.add next 4#64)) isStack addr 64
      (by decide) (imm.signExtend 64) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address 64 isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_any _ (hu.withNextIP (BitVec.add next 4#64)) isStack addr 32
      (by decide) (imm.signExtend 32) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address 64 isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

theorem mov_m64_imm32_step_any [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (7 + am.tail.length)) 8) :
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
  rw [mov_m_imm32_form_any _ _ u _ _ _ _ 64 (.inl rfl) (hrex.operand_size s.DS) rfl rfl _ _ _ _ _ imm
    hea himm hrip hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC7 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m64_imm32_effect_step_any [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (Pre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32Effect p am imm) :=
  effect_step_of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_imm32_step_any s h rex hrex am hv hx hb imm hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem decodeLegacy0_run_of_C7_memory_any [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0xC7 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0xC7 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMv_IMMz_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeC7 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0OpcodeC7_run_of_memory _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

theorem mov_m32_imm32_legacy_step_any [Bindings] (s : RamState) (h : ReadyToStep s) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (6 + am.tail.length)) 4) :
    X86.Machine.step s = some (.next (afterStep s (6 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (6 + am.tail.length)) : Operand 32)
        (movSpec (imm.signExtend 32)) (BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_C7_memory_any s h (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j hj => getElem?_cons2_append _ _ _ _ j hj) (by simp; omega) (by omega)
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length)) := hea
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (3 + am.tail.length) h.fetchReady hc hlow' 32
    (by decide) imm (2 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (0xC7 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + j = 2 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 3 + am.tail.length + 32 / 8 = 6 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (6 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 4#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (6 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (2 + am.tail.length) 4
    rw [show 2 + am.tail.length + 4 = 6 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 4#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (6 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  rw [mov_m_imm32_form_any _ _ u _ _ _ _ 32 (.inr rfl) rfl rfl rfl _ _ _ _ _ imm
    hea himm hrip hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC7 _
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def movM32Imm32LegacyEffect (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) : RamState → Effect :=
  storeEffect p (6 + am.tail.length) (storeAddrAt p am (6 + am.tail.length)) fun _ => imm

theorem mov_m32_imm32_legacy_effect_step_any [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (Pre p (6 + am.tail.length) (storeAddrAt p am (6 + am.tail.length)) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32LegacyEffect p am imm) :=
  effect_step_of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      simpa only [BitVec.signExtend_eq, movSpec, storeAddrAt, AddrMode.addrAt, BitVec.add_eq] using
        mov_m32_imm32_legacy_step_any s h am hv hx hb imm hcode.bytesAt
          (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Hkdf.Proofs.Common.Instructions.CrossPageStore
