import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers
open P256.Proofs.Common.Encoding.Parser.LengthCheck

theorem decodeLegacy0_run_of_opcode39 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x39, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_39 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode39_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_39 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_39, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode39_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_39 ip context).run s =
      (X86.Instructions.CMP_MEMv_GPRv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_39
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_39 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0Opcode39_run_of_memory context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy0_run_of_rex_39_memory [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0x39 :: modrm :: rest))
    (hlow : s.RIP.toNat + (rex :: 0x39 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.CMP_MEMv_GPRv (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x39 :: modrm :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x39, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode39 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode39_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl


theorem cmp_m64_r64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hread : MemReadable t addr 8) :
    (X86.Instructions.CMP_MEMv_GPRv ip ctx mod reg rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read t) ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t)) 0 next) := by
  have hcontext :
      {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hload := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hread.low hread.mem
  unfold X86.Instructions.CMP_MEMv_GPRv
  simp only [writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  simp only [hrip]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    Logical_Mem_Read => hload,
    X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]


theorem cmp_m64_r64_step_of_address [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm ≠ 3)
    (rest : List UInt8) (addr off : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hcode : BytesAt s s.RIP (rex :: 0x39 :: modrm :: rest))
    (hlow : s.RIP.toNat + (3 + rest.length) ≤ 2^32)
    (hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) (modrmMod modrm)
      (modrmRm modrm) 1 (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (off, flatData isStack, BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length)), isRip, baseUsesRsp),
        afterFetches (beforeFetch s) (3 + rest.length + 1)))
    (hrip : Handle_RIP_Relative_Address 64 isRip off
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length))) = .ok addr)
    (hread : MemReadable s addr 8) :
    X86.Machine.step s = some (.next (afterStep s (3 + rest.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read t) ((Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) :
          Operand 64).read t)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + rest.length))))) := by
  have hlow' : s.RIP.toNat + (rex :: 0x39 :: modrm :: rest).length ≤ 2^32 := by
    simp only [List.length_cons]
    omega
  have hd := decodeLegacy0_run_of_rex_39_memory s h rex modrm hmod rest hcode hlow'
  let t := afterFetches (beforeFetch s) (3 + rest.length + 1)
  have hm : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  erw [cmp_m64_r64_form _ t _ _ _ (modrmReg modrm) _ (hrex.operand_size _) rfl rfl
    _ _ _ _ _ hea hrip ht hm (hread.of_external_eq rfl)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x39 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hd
    (hm.of_cs_lma_eq rfl rfl)


def cmpM64R64Effect (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (addr : RamState → BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags
      (cmpSpec ((Operand.mem (addr s) : Operand 64).read s) ((Operand.reg src : Operand 64).read s))) }

theorem cmp_m64_r64_effect_holds [Bindings] {s : RamState} (h : ReadyToStep s)
    (p : BitVec 64) (len : Nat) (src : BitVec 5) (addr : RamState → BitVec 64) :
    (cmpM64R64Effect p len src addr s).Holds s (afterStep s len fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem (addr s) : Operand 64).read t) ((Operand.reg src : Operand 64).read t)) 0 (p + BitVec.ofNat 64 len)) := by
  refine ⟨afterStep_loadFlags_rip h _ _ _, trivial, ?_,
    AgreesExcept.afterStep_loadFlags s len _ _⟩
  change (StatusFlagsOutcome.ofStatusFlags
    (cmpSpec ((Operand.mem (addr s) : Operand 64).read s) ((Operand.reg src : Operand 64).read s))).Allows
    (StatusFlags.ofRFLAGS ((cmpSpec
      ((Operand.mem (addr s) : Operand 64).read (afterFetches (beforeFetch s) (len + 1)))
      ((Operand.reg src : Operand 64).read (afterFetches (beforeFetch s) (len + 1)))).store s.RFLAGS))
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _

theorem cmp_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x39 :: am.modrm reg :: am.tail))
      (cmpM64R64Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length)))) := by
  rintro s h hcode ⟨rfl, hread⟩
  have hlow : s.RIP.toNat + (rex :: 0x39 :: am.modrm reg :: am.tail).length ≤ 2^32 :=
    hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow 3
    (fun j _ => getElem?_cons3 _ _ _ _ j) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  have ha : am.addr (beforeFetch s)
      (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
        am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) :=
    AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [ha] at hrip
  have hs := cmp_m64_r64_step_of_address s h rex (am.modrm reg) hrex
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail _ _ _ _
    hcode.bytesAt (by simp only [List.length_cons] at hlow; omega)
    (by simpa only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm,
      show (beforeFetch s).RIP = s.RIP from rfl] using hea) hrip hread
  simp only [AddrMode.modrmReg_modrm] at hs
  exact ⟨_, hs, ReadyToStep.afterStep_loadFlags h _ _ _,
    cmp_m64_r64_effect_holds h _ _ _ _⟩


end P256.Proofs.Common.Instructions
