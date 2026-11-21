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
import X86Proofs.Instructions.And.Operation
import Base16ct.Proofs.EncodeStr.Lower.Machine.Instructions.ByteAlu.Add
import X86Proofs.Step.Decode.Legacy0

namespace Base16ct.Proofs.EncodeStr.Lower

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem selectLegacy0Opcode80_run_of_r4_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0Opcode80_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.AND_GPR8_IMMb_80r4 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦
      selectLegacy0Opcode80_run_of_r4_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_80_r4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (rex :: 0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.AND_GPR8_IMMb_80r4 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x80, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow' 2 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode80 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode80_run_of_r4_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem and_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.AND_GPR8_IMMb_80r4 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.AND_GPR8_IMMb_80r4
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    Write_GPR8 => Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte.writeGPR8_run_of_rex _ _ _
      (htmode.of_cs_lma_eq rfl rfl)]

theorem and_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (rex :: 0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) imm) 1
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_80_r4 s h rex modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hc hlow'
    8 (by decide) imm 3
    (immBytes_getElem?_append [rex, 0x80, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [and_r8_imm8_form _ _ (BitVec.add s.RIP 3#64) _ _ imm (hmode 4)
    rfl rfl himm (hmode 5), BitVec.signExtend_eq,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0x80 (modrm :: immBytes 8 imm) hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    ((hmode 5).of_cs_lma_eq rfl rfl)

def andR8Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s &&& imm
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (andFlags r) }

theorem andR8Imm8Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) :
    (andR8Imm8Effect p dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem andR8Imm8Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (andR8Imm8Effect p dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [andR8Imm8Effect_components, Component.Covers]) code

theorem and_r8_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (andR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_r8_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 4 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte.read_writeOutputs_self8]
    simp only [andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    Triple (fun s ↦ s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (Effect.post (andR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ ↦ andR8Imm8Effect_avoids p _ _ s _)
    (and_r8_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem and_r11b_imm27_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe3, 0x27])
      (andR8Imm8Effect p 11 0x27) := by
  simpa only [show immBytes 8 (0x27 : BitVec 8) = [0x27] from by decide +kernel,
    show gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (modrmRm 0xe3) = 11
      from by decide +kernel] using
    and_r8_imm8_effect_step p 0x41 0xe3 0x27 (by unfold RexPrefix; decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem and_r10b_imm27_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe2, 0x27])
      (andR8Imm8Effect p 10 0x27) := by
  simpa only [show immBytes 8 (0x27 : BitVec 8) = [0x27] from by decide +kernel,
    show gprNumber 0 (rexB (0x41 : UInt8).toBitVec) (modrmRm 0xe2) = 10
      from by decide +kernel] using
    and_r8_imm8_effect_step p 0x41 0xe2 0x27 (by unfold RexPrefix; decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem and_r11b_imm27_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe3, 0x27])
      (Effect.post (andR8Imm8Effect p 11 0x27)) :=
  Triple.of_effect (fun s _ ↦ andR8Imm8Effect_avoids p _ _ s _)
    (and_r11b_imm27_effect_step p)

theorem and_r10b_imm27_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x41, 0x80, 0xe2, 0x27])
      (Effect.post (andR8Imm8Effect p 10 0x27)) :=
  Triple.of_effect (fun s _ ↦ andR8Imm8Effect_avoids p _ _ s _)
    (and_r10b_imm27_effect_step p)

theorem andR8Imm8Effect.read8 {p : BitVec 64} {dst : BitVec 5} {imm : BitVec 8}
    {s t : RamState} (h : (andR8Imm8Effect p dst imm s).Holds s t) :
    (Operand.reg dst : Operand 8).read t = (Operand.reg dst : Operand 8).read s &&& imm := by
  have hw := h.writes
  change (Operand.reg dst : Operand 64).read t = _ at hw
  change ((Operand.reg dst : Operand 64).read t).setWidth 8 = _
  rw [hw, Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte.mergeGPR8_setWidth]

attribute [x86_compose] andR8Imm8Effect

@[x86_local] theorem andR8Imm8Effect_local : Effect.Local (andR8Imm8Effect p dst imm) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h ↦ ?_,
    fun t t' h i hi ↦ ?_, fun t ↦ ?_⟩
  · rfl
  · simp only [andR8Imm8Effect, h.read_reg]
  · rfl
  · cases i <;> simp [andR8Imm8Effect, Effect.flag, andFlags,
      StatusFlagsOutcome.get, h.read_reg]
  · simp [andR8Imm8Effect, Write.Full, Operand.Full]

end Base16ct.Proofs.EncodeStr.Lower
