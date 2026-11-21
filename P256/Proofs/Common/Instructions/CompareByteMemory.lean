import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.CompareByteMemory

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectLegacy0Opcode80_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode80_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.CMP_MEMb_IMMb_80r7 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 6 2) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r7_memory context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_80_r7_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 7) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x80)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CMP_MEMb_IMMb_80r7 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x80 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode80 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode80_run_of_r7_memory a u _ ctx _ hmod hreg hmode hfe hf)

theorem cmp_m8_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u) (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMP_MEMb_IMMb_80r7 ip ctx mod rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess u "load")
        (cmpSpec ((Operand.mem addr : Operand 8).read u) (imm.signExtend 8)) 0
        (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 8 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  have hcontext :
      {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_MEMb_IMMb_80r7
  simp only [writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

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
      pre.length + 3 + am.tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
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

def cmpM8Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s)
      (imm.signExtend 8))) }

theorem cmp_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x80 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := cmp_m8_imm8_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) imm hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmpM8Imm8Effect_ZF {p : BitVec 64} {len : Nat} {am : AddrMode} {imm : BitVec 8}
    {s t : RamState} (h : (cmpM8Imm8Effect p len am imm s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      decide ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s =
        imm.signExtend 8) := by
  have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      (cmpSpec ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s)
        (imm.signExtend 8)).ZF := h.flags.2.2.2.1
  rw [hz]
  simp only [cmpSpec, subSpec]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  change (_ = BitVec.add 0#8 (imm.signExtend 8)) ↔ _
  have hzadd : BitVec.add 0#8 (imm.signExtend 8) = imm.signExtend 8 := BitVec.zero_add _
  rw [hzadd]

theorem cmp_rsp_disp8_imm8_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 8)
    (imm : UInt8) :
    StepEffect (LoadPre p (fun s => (Operand.reg 4 : Operand 64).read s + disp.signExtend 64) 1)
      (codeRange p [0x80, 0x7c, 0x24, UInt8.ofBitVec disp, imm])
      (cmpM8Imm8Effect p 5 (.sib 4 none 0 (.d8 disp)) imm.toBitVec) := by
  have hm : (AddrMode.sib 4 none 0 (.d8 disp)).modrm 7 = 0x7c := by
    simp [AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod]
  have h := cmp_m8_imm8_effect_step p (.sib 4 none 0 (.d8 disp))
    ⟨by decide, fun _ => by decide⟩ rfl rfl imm
  rw [hm] at h
  simpa [AddrMode.tail, AddrMode.sibByte, idxLow, regLow, Disp.bytes, immBytes_eight, AddrMode.addr, Disp.value, AddrMode.reg64, Operand.read] using h

attribute [x86_compose] cmpM8Imm8Effect

end P256.Proofs.Common.Instructions.CompareByteMemory
