import P256.Proofs.Common.Instructions.ByteLogic.Core
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Program.ReadWrite.LoadFlags
import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteLogic

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open scoped X86.Runtime.Syntax

theorem xor_r8_m8_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_GPR8_MEMb ip ctx mod reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let u := dataAccess t "load"
      (.ok (), writeOutputs u dst
        (xorSpec (oracleBit u.oracle) (dst.read t) ((Operand.mem addr : Operand 8).read t)) 1 next) := by
  have hctx : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hctx]
  have hread := logicalMemRead_run t ht isStack addr 8 (by decide) .Memory_Read (.inl rfl) hlow hmem
  unfold X86.Instructions.XOR_GPR8_MEMb
  simp only [writeOutputs, Operand.write, Operand.read]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (readGPR8_run _ _ _ haccess hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread,
    X86.Instructions.Operations.XOR => xor_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0Opcode32_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_32 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_32, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode32_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_32 ip context).run s =
      (X86.Instructions.XOR_GPR8_MEMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_32
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_32 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy0Opcode32_run_of_memory context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy0_run_of_32_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x32 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x32 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.XOR_GPR8_MEMb (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode32 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode32_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem xor_r8_m8_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (reg : BitVec 3) (hsmall : (gprNumber 0 0 reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x32 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (2 + am.tail.length)) 1) :
    let dst : Operand 8 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeOutputs (dataAccess t "load") dst
        (xorSpec (oracleBit (dataAccess t "load").oracle) (dst.read t)
          ((Operand.mem (am.addrAt s (2 + am.tail.length)) : Operand 8).read t)) 1 (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x32 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_32_memory s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x32 :: am.modrm reg :: am.tail) := hcode
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
  rw [xor_r8_m8_form _ t (BitVec.add s.RIP 2#64) (legacyContext s.DS) am.mod reg am.rm rfl rfl (.inr hsmall) _ _ _ _ _ hea hrip ht hmode
    hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x32 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def xorR8M8LegacyEffect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s ^^^
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 8).read s
  { rip := p + BitVec.ofNat 64 (2 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (xorFlags r) }

theorem xorR8M8LegacyEffect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (xorR8M8LegacyEffect p dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem xor_r8_m8_legacy_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hsmall : (gprNumber 0 0 reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x32 :: am.modrm reg :: am.tail))
      (xorR8M8LegacyEffect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, xor_r8_m8_legacy_step s h reg hsmall am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, xorSpec,
      dataAccess, afterFetches, beforeFetch, resetStepFields, AddrMode.addrAt]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_al_rsp4c_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LoadPre p (fun s => (Operand.reg 4 : Operand 64).read s + 0x4c) 1)
      (codeRange p [0x32, 0x44, 0x24, 0x4c])
      (xorR8M8LegacyEffect p 0 (.sib 4 none 0 (.d8 0x4c))) := by
  refine (xor_r8_m8_legacy_effect_step p 0 (by decide +kernel)
    (.sib 4 none 0 (.d8 0x4c)) (by simp [AddrMode.Valid]) rfl rfl).mono_pre ?_
  intro s h
  refine ⟨h.1, ?_⟩
  simpa [AddrMode.addr, AddrMode.reg64, Disp.value] using h.2

end P256.Proofs.Common.Instructions.ByteLogic
