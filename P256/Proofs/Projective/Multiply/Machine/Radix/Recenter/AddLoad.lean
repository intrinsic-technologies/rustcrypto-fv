import P256.Proofs.Common.Instructions.ByteLogic.Core
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Add.Operation
import X86Proofs.Program.ReadWrite.LoadFlags

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteLogic (writeGPR8_run)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_r8_m8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (hreg : (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hr : MemReadable t addr 1) :
    (X86.Instructions.ADD_GPR8_MEMb ip ctx mod reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs (dataAccess t "load") dst
        (addSpec (dst.read t) ((Operand.mem addr : Operand 8).read t)) 0 next) := by
  have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 8 (by decide) .Memory_Read (.inl rfl)
    hr.low hr.mem
  unfold X86.Instructions.ADD_GPR8_MEMb
  simp only [writeOutputs, Operand.read, Operand.write]
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR8_run_of_low _ _ hreg _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ (.inr hreg) (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0_run_of_opcode02 [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x02, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_02 ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0Opcode02_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_0_Opcode_02 ip ctx).run s =
      (X86.Instructions.ADD_GPR8_MEMb (BitVec.add ip 2#64) ctx (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_02 ctx true a b c d e f modrm = .ok 2 := by
    simp [Select_Legacy_0_Opcode_02, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_02
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem decodeLegacy0_run_of_02_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0x02 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x02 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.ADD_GPR8_MEMb (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode02 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode02_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem add_r8_m8_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3)
    (hreg : (gprNumber 0 0 reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x02 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32)
    (hw : MemReadable s (am.addrAt s (2 + am.tail.length)) 1) :
    let dst : Operand 8 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t =>
      writeOutputs (dataAccess t "load") dst
        (addSpec (dst.read t) ((Operand.mem (am.addrAt s (2 + am.tail.length)) : Operand 8).read t)) 0 (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x02 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_02_memory s h (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x02 :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ => by rw [show 2 + j = j + 1 + 1 by omega]; rfl)
    (by simp; omega) (by have := am.tail_length_le; omega)
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
  rw [add_r8_m8_form (afterFetches (beforeFetch s) 3) t (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) am.mod reg am.rm rfl rfl hreg _ _ _ _ _ hea hrip ht hmode
    (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x02 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def addR8M8Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let result := addSpec ((Operand.reg dst : Operand 8).read s)
    ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 8).read s)
  { rip := p + BitVec.ofNat 64 (2 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64), mergeGPR 8 result.1 ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags result.2) }

theorem add_r8_m8_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (hreg : (gprNumber 0 0 reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x02 :: am.modrm reg :: am.tail))
      (addR8M8Effect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨rfl,hr⟩
  have hl : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, add_r8_m8_step s h reg hreg am hv hx hb hcode.bytesAt hl hr,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, addSpec, setFlags,
      dataAccess, AddrMode.addrAt, afterFetches, beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

@[x86_local] theorem addR8M8Effect_local (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    Effect.Local (addR8M8Effect p dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [addR8M8Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro s
    simp [addR8M8Effect, Write.Full, Operand.Full]

attribute [x86_compose] addR8M8Effect

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
