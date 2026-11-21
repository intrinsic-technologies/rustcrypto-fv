import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovStore.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare.Initialize

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem mov_m8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Sha1.Proofs.Common.Instructions.StorePre.MemWritable s
      (am.addrAt s (3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_C6_memory s h (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _
    hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j hj => getElem?_cons2_append _ _ _ _ j hj) (by simp; omega) (by omega)
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (3 + am.tail.length) h.fetchReady hc
    hlow' 8 (by decide) imm (2 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (0xC6 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + j = 2 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 3 + am.tail.length + 8 / 8 = 3 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.memory.tables
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
  rw [Sha1.Proofs.Common.Instructions.MovStore.mov_m8_imm8_form _ _ u _ _ _ _ rfl rfl _ _ _ _ _
    imm hea himm hrip _ (SegAccess.flat _ _) hu (hw.of_external_eq rfl)] at hdecode
  rw [show (beforeFetch s).RIP = s.RIP from rfl, hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC6 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode
    hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.StorePre p (3 + am.tail.length)
        (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8Effect p am imm) := by
  refine Sha1.Proofs.Common.Instructions.Store.storeEffect_step (n := 8) (by decide) (by decide)
    _ _ fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have step := mov_m8_imm8_step s h am hv hx hb imm hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw
  simpa only [movSpec, BitVec.signExtend_eq, storeAddrAt, AddrMode.addrAt, BitVec.add_eq]
    using step

end Sha1.Proofs.Buffered.DigestPrepare.Initialize
