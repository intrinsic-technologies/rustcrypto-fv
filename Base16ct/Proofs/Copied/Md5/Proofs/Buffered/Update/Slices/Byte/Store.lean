import Base16ct.Proofs.Copied.Md5.Proofs.Memory.Basic
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
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

namespace Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode88 [Bindings]
    (s u : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x88, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_88 ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode88_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_88 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_88, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode88_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_88 ip context).run s =
      (X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_88
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦ selectLegacy0Opcode88_run_of_memory context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_pfx_88_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (pfx modrm : UInt8)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pfx :: 0x88 :: modrm :: rest))
    (hlow : s.RIP.toNat + (pfx :: 0x88 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) ctx).run (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP 3#64) ctx (modrmMod modrm)
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode88 _ _ _ _ hrex2 f2 (hmode 3),
    decodeLegacy0Opcode88_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem decodeLegacy0_run_of_88_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x88 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x88 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode88 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode88_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem mov_m8_r8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable t addr 1)
    (hread : (Read_GPR8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (ctx.rex_prefix_present || ctx.rex2_prefix_present || ctx.vex_prefix_present ||
        ctx.evex_prefix_present)).run t =
      (.ok ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t), t)) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand 8)
        ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t) next) := by
  have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := Base16ct.Proofs.Copied.Md5.Proofs.Memory.logicalMemWrite_run _ (ht.withNextIP next) isStack addr 8
    (by decide) ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t)
    hw.low hw.bytes
  unfold X86.Instructions.MOV_MEMb_GPR8_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with hread
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

theorem mov_m8_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x88 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (am.addrAt s (3 + am.tail.length)) 1) :
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t ↦
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (rex :: 0x88 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_pfx_88_memory s h rex (am.modrm reg)
    (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x88 :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ ↦ getElem?_cons3 _ _ _ _ j) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
      am.addrAt s (3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_m8_r8_form _ t _ _ _ _ _ rfl rfl _ _ _ _ _ hea hrip ht
    (hw.of_external_eq rfl) (readGPR8_run_of_rex _ _ hmode)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0x88 _ hrex (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hreg : (gprNumber 0 0 reg).toNat < 4)
    (hcode : BytesAt s s.RIP (0x88 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (am.addrAt s (2 + am.tail.length)) 1) :
    let src : Operand 8 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t ↦
      writeResult (dataAccess t "store") (.mem (am.addrAt s (2 + am.tail.length)) : Operand 8)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (0x88 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_88_memory s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x88 :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ ↦ by
      simp only [show 2 + j = j + 1 + 1 by omega, List.getElem?_cons_succ])
    (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 3 + am.tail.length = 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) =
      am.addrAt s (2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_m8_r8_form _ t _ _ _ _ _ rfl rfl _ _ _ _ _ hea hrip ht
    (hw.of_external_eq rfl) (readGPR8_run_of_low _ _ hreg false hmode)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0x88 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def movM8R8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (storeAddrAt p am len) fun s ↦ (Operand.reg src : Operand 8).read s

theorem mov_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre p (3 + am.tail.length)
      (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Base16ct.Proofs.Copied.Md5.Proofs.Memory.stepEffect_of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre ↦ by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m8_r8_rex_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m8_r8_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hreg : (gprNumber 0 0 reg).toNat < 4) :
    StepEffect (Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre p (2 + am.tail.length)
      (storeAddrAt p am (2 + am.tail.length)) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am) :=
  Base16ct.Proofs.Copied.Md5.Proofs.Memory.stepEffect_of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre ↦ by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m8_r8_step s h reg am hv hx hb hreg hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

attribute [x86_compose] movM8R8Effect

@[x86_local] theorem movM8R8Effect_local (p : BitVec 64) (len : Nat)
    (src : BitVec 5) (am : AddrMode) : Effect.Local (movM8R8Effect p len src am) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movM8R8Effect, storeEffect, AddrMode.addr_obs h]
  · simp [movM8R8Effect, storeEffect, h.read_reg, AddrMode.addr_obs h]
  · simpa only [movM8R8Effect, storeEffect, Effect.flag] using congrArg some hi
  · simp [movM8R8Effect, storeEffect, Write.Full, Operand.Full]

end Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte
