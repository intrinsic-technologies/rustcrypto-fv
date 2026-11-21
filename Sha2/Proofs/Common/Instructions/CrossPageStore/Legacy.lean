import Sha2.Proofs.Common.Instructions.CrossPageStore.Mov

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_89_memory_any [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x89 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x89 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMv_GPRv_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode89 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode89_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem mov_m32_r32_legacy_step_any [Bindings] (s : RamState) (h : ReadyToStep s)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hw : Writable s (am.addrAt s (2 + am.tail.length)) 4) :
    let src : Operand 32 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (2 + am.tail.length)) : Operand 32)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_89_memory_any s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x89 :: am.modrm reg :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ => by simp only [show 2 + j = j + 1 + 1 by omega, List.getElem?_cons_succ]) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 3 + am.tail.length = 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) =
      am.addrAt s (2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_m_r_form_any _ t _ _ _ _ _ 32 (.inr rfl) rfl rfl rfl _ _ _ _ _ hea hrip ht hmode
    (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x89 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def movM32R32LegacyEffect (p : BitVec 64) (src : BitVec 5) (am : AddrMode) : RamState → Effect :=
  storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
    fun s => (Operand.reg src : Operand 32).read s

theorem mov_m32_r32_legacy_effect_step_any [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Pre p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length)) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (movM32R32LegacyEffect p (gprNumber 0 0 reg) am) :=
  effect_step_of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_legacy_step_any s h reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end Sha2.Proofs.Common.Instructions.CrossPageStore
