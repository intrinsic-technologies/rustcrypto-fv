import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.Compose
import X86Proofs.Step.Escape

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

theorem decodeLegacy1_run_of_opcodeBF [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode u) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xbf, u)) :
    (Decode_Legacy_1 ip ctx).run s = some ((Decode_Legacy_1_Opcode_BF ip ctx).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1OpcodeBF_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BF ctx true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeBF_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip ctx).run s =
      (X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_BF ctx mode a b c d e f modrm) _ 4 hmode hf
    (fun a b c d e f ↦ selectLegacy1OpcodeBF_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem selectLegacy1OpcodeB6_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B6 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB6_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip ctx).run s =
      (X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_B6 ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1OpcodeB6_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem movsx_r32_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ]
    (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVSX_GPRv_GPR16 ip ctx reg rm).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s).signExtend 32)
        ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVSX_GPRv_GPR16
  simp only [writeResult, Operand.write_reg32]
  repeat spec_bind_rfl
  spec_bind_with readGPR16_run _ _ hmode
  repeat spec_bind_rfl
  erw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
  rfl

theorem decodeLegacy1_run_of_rex_BF_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xBF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0xBF, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xBF, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 hf hc hlow 3 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcodeBF _ _ _ _ rfl (hmode 4) f2,
    decodeLegacy1OpcodeBF_run_of_register _ _ _ _ _ hmod (hmode 5) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem movsx_r32_r16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xBF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeResult t (.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 32)
        (((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read t).signExtend 32)
        (BitVec.add s.RIP 4#64))) := by
  have hd := decodeLegacy1_run_of_rex_BF_register s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [movsx_r32_r16_form _ _ _ _ _ hmode (hrex.operand_size _) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy1 s _ h rex 0xBF [modrm] hrex.rexPrefix (by decide) hcode hlow hd
    (hmode.of_cs_lma_eq rfl rfl)

def movsxReg32Reg16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      (((Operand.reg src : Operand 16).read s).signExtend 32).setWidth 64⟩] }

theorem movsxReg32Reg16Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (movsxReg32Reg16Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem movsxReg32Reg16Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (movsxReg32Reg16Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [movsxReg32Reg16Effect_components, Component.Covers]) code

theorem movsx_r32_r16_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x0F, 0xBF, modrm])
      (movsxReg32Reg16Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movsx_r32_r16_step s h rex modrm hrex hmod hcode.bytesAt
      (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem readGPR8_bh_run {σ : Type} (s : X86.State σ) (hmode : In64BitMode s) :
    (Read_GPR8 7 false).run s = (.ok (s.GPR[gprIndex 3].extractLsb' 8 8), s) := by
  unfold Read_GPR8
  rw [specM_bind_run _ _ hmode]
  rfl

theorem movzx_ebx_bh_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ds : Segment) (hmode : In64BitMode s) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip (legacyContext ds) 3 7).run s =
      (.ok (), writeResult s (.reg 3 : Operand 32)
        ((((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 32) ip) := by
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.write_reg32]
  repeat spec_bind_rfl
  spec_bind_with readGPR8_bh_run _ hmode
  repeat spec_bind_rfl
  erw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
  simp only [BitVec.ofNat_toNat]
  rfl

theorem movzx_ebx_bh_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x0F, 0xB6, 0xDF]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeResult t (.reg 3 : Operand 32)
        ((((Operand.reg 3 : Operand 64).read t).extractLsb' 8 8).setWidth 32)
        (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0F, 0xB6, 0xDF] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok 0xDF, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB6 _ _ (BitVec.add s.RIP 1#64)
    (legacyContext s.DS) rfl (hmode 3) f1
  rw [decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ rfl (hmode 4) hf f2] at hd
  change _ = some ((X86.Instructions.MOVZX_GPRv_GPR8 _ (legacyContext s.DS) 3 7).run _) at hd
  rw [movzx_ebx_bh_form _ _ _ (hmode 4),
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy1 s _ h 0xB6 [0xDF] (by decide) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def movzxEbxBhEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 3 : Operand 64),
      (((Operand.reg 3 : Operand 64).read s).extractLsb' 8 8).setWidth 64⟩] }

theorem movzxEbxBhEffect_components (p : BitVec 64) (s : RamState) :
    (movzxEbxBhEffect p s).components = [.reg 3, .rip] := rfl

theorem movzxEbxBhEffect_avoids (p : BitVec 64) (s : RamState) (code : CodeMap) :
    (movzxEbxBhEffect p s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [movzxEbxBhEffect_components, Component.Covers]) code

theorem movzx_ebx_bh_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0xB6, 0xDF]) (movzxEbxBhEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_ebx_bh_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

attribute [x86_compose] movsxReg32Reg16Effect movzxEbxBhEffect

@[x86_local] theorem movsxReg32Reg16Effect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (movsxReg32Reg16Effect p dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movsxReg32Reg16Effect, h.read_reg]
  · simpa only [movsxReg32Reg16Effect, Effect.flag] using congrArg some hi
  · simp [movsxReg32Reg16Effect, Write.Full, Operand.Full]

@[x86_local] theorem movzxEbxBhEffect_local (p : BitVec 64) :
    Effect.Local (movzxEbxBhEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movzxEbxBhEffect, h.read_reg]
  · simpa only [movzxEbxBhEffect, Effect.flag] using congrArg some hi
  · simp [movzxEbxBhEffect, Write.Full, Operand.Full]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
