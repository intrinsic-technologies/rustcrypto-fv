import P256.Proofs.Common.EffectCompose
import X86Proofs.Instructions.Inc.Operation
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.Increment

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem inc_m64_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 64) (haddr : ctx.address_size = 64)
    (off next addr : BitVec 64) (isStack isRip baseUsesRsp : Bool)
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.INC_MEMv ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs t addr
        (incSpec (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.mem addr : Operand 64).read t))
        0 next) := by
  have hcontext : {ctx with operand_size := 64, address_size := 64} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run t ht isStack addr 64 (by decide) .Memory_Read_Modify_Write
    (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) isStack addr 64 (by decide) v hlow hmem
  unfold X86.Instructions.INC_MEMv
  simp only [writeRmwOutputs, writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread,
    X86.Instructions.Operations.INC => inc_operation _ 64 (by decide) _,
    Logical_Mem_Write => hwrite _ _]

theorem selectLegacy0OpcodeFF_run_of_inc_memory (context : Instruction_Context) (hlock : context.lock_prefix_present = false) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 0#3) :
    Select_Legacy_0_Opcode_FF context true a b c d e f modrm = .ok 13 := by
  simp [Select_Legacy_0_Opcode_FF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd, hlock]

theorem decodeLegacy0OpcodeFF_run_of_inc_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hlock : context.lock_prefix_present = false) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 0#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_FF ip context).run s =
      (X86.Instructions.INC_MEMv (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_FF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeFF_run_of_inc_memory context hlock a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_FF_inc_memory [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0xFF :: modrm :: rest)) (hlow : s.RIP.toNat + (rex :: 0xFF :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.INC_MEMv (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0xFF :: modrm :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xFF, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeFF _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeFF_run_of_inc_memory _ _ _ _ rfl _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem inc_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0xFF :: am.modrm 0 :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) 8) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeRmwOutputs t (am.addrAt s (3 + am.tail.length))
        (incSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t))
        0 (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have hlow' : s.RIP.toNat + (rex :: 0xFF :: am.modrm 0 :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_rex_FF_inc_memory s h rex (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0xFF :: am.modrm 0 :: am.tail) :=
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
  rw [inc_m64_form _ t _ _ _ _ (hrex.operand_size s.DS) rfl _ _ _ _ _ _ hea hrip ht hread.low
    hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xFF _ hrex.rexPrefix (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def incM64Effect (p : BitVec 64) (am : AddrMode) (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))
  let out := incSpec (StatusFlags.ofRFLAGS s.RFLAGS) ((Operand.mem addr : Operand 64).read s)
  { rip := p + BitVec.ofNat 64 (3 + am.tail.length)
    writes := [⟨(Operand.mem addr : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem incM64Effect_components (p : BitVec 64) (am : AddrMode) (s : RamState) :
    (incM64Effect p am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8, .flags, .rip] := by
  simp [incM64Effect, Effect.components]

theorem inc_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (3 + am.tail.length))
      (codeRange p (rex :: 0xff :: am.modrm 0 :: am.tail))
      (incM64Effect p am) := by
  intro s h hcode hpre
  obtain ⟨hp, hw, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, inc_m64_step s h rex hrex am hv hx hb hcode.bytesAt hlow hw.readable,
    ReadyToStep.afterStep_rmw h _ _ _ _ _ hw.low hw.tables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

attribute [x86_compose] incM64Effect incSpec

theorem inc_rsp1a0_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (StorePre p 8 (fun s => (Operand.reg 4 : Operand 64).read s + 0xf8) 8)
      (codeRange p [0x48, 0xff, 0x84, 0x24, 0xf8, 0x00, 0x00, 0x00])
      (incM64Effect p (.sib 4 none 0 (.d32 0xf8))) := by
  refine (inc_m64_effect_step p 0x48 (by unfold RexWPrefix; decide +kernel)
    (.sib 4 none 0 (.d32 0xf8)) (by simp [AddrMode.Valid]) rfl rfl).mono_pre ?_
  intro s h
  change StorePre p 8 _ 8 s
  simpa [AddrMode.addr, AddrMode.reg64, Disp.value] using h

end P256.Proofs.Nonce.Update.Absorb.Seeded.Increment
