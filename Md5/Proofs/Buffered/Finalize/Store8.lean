import Md5.Proofs.Buffered.Stores.Effect
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.Buffered.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem decodeLegacy0_run_of_pfx_C6_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (pfx modrm : UInt8) (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pfx :: 0xC6 :: modrm :: rest))
    (hlow : s.RIP.toNat + (pfx :: 0xC6 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) ctx).run (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_MEMb_IMMb_1 (BitVec.add s.RIP 3#64) ctx (modrmMod modrm)
        (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeC6 _ _ _ _ hrex2 f2 (hmode 3),
    decodeLegacy0OpcodeC6_run_of_memory _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem mov_m8_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hw : Md5.Proofs.Memory.MemWritable s (am.addrAt s (4 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (4 + am.tail.length)) : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_pfx_C6_memory s h rex (am.modrm 0) (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j hj => getElem?_cons3_append _ _ _ _ _ j hj) (by simp; omega) (by omega)
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (4 + am.tail.length)) := hea
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (4 + am.tail.length) h.fetchReady hc hlow' 8
    (by decide) imm (3 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (rex :: 0xC6 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + 1 + j = 3 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 4 + am.tail.length + 8 / 8 = 4 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (4 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (3 + am.tail.length) 1
    rw [show 3 + am.tail.length + 1 = 4 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 1#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (4 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  rw [Stores.mov_m8_imm8_form _ _ u _ _ _ _ rfl rfl _ _ _ _ _ imm
    hea himm hrip hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC6 _ hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def movM8Imm8RexEffect (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) : RamState → Effect :=
  storeEffect p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)) (fun _ ↦ imm)

theorem mov_m8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (Md5.Proofs.Memory.StorePre p (4 + am.tail.length)
      (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8RexEffect p am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine Md5.Proofs.Memory.stepEffect_of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre ↦ ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have := mov_m8_imm8_rex_step s h rex hrex am hv hx hb imm hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw
  rwa [movSpec, hse] at this

attribute [x86_compose] movM8Imm8RexEffect

@[x86_local] theorem movM8Imm8RexEffect_local : Effect.Local (movM8Imm8RexEffect p am imm) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h ↦ ?_,
    fun t t' h i hi ↦ ?_, fun t ↦ ?_⟩
  · rfl
  · simp only [movM8Imm8RexEffect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · rfl
  · simpa only [movM8Imm8RexEffect, storeEffect, Effect.flag] using congrArg some hi
  · simp [movM8Imm8RexEffect, storeEffect, Write.Full, Operand.Full]

end Md5.Proofs.Buffered.Finalize
