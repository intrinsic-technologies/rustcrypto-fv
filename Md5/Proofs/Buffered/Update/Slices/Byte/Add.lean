import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
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

namespace Md5.Proofs.Buffered.Update.Byte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode00 [Bindings]
    (s u : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_00 ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode00_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_00 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode00_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_00 ip context).run s =
      (X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦ selectLegacy0Opcode00_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_rex_00 [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [rex, 0x00, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x00, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x00, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode00 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode00_run_of_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem writeGPR8_run_of_rex {σ : Type} (s : X86.State σ) (r : BitVec 5)
    (value : BitVec 8) (mode : In64BitMode s) :
    (Write_GPR8 r true value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) }) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

theorem add_r8_r8_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (addSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem add_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x00, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeOutputs t dst (addSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_00 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [add_r8_r8_form _ _ _ _ _ hmode rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x00 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

def addR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem addR8R8Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (addR8R8Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem addR8R8Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (addR8R8Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [addR8R8Effect_components, Component.Covers]) code

theorem read_writeOutputs_self8 (s : RamState) (r : BitVec 5)
    (out : BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read
      (writeOutputs s (.reg r : Operand 8) out oracleUsed nextIP) =
      mergeGPR 8 out.1 ((Operand.reg r : Operand 64).read s) := by
  simp [writeOutputs, setFlags, Operand.read, Operand.write]

theorem add_r8_r8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x00, modrm])
      (addR8R8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, add_r8_r8_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, read_writeOutputs_self8]
    simp only [addSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem mergeGPR8_setWidth (v : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 v old).setWidth 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change ((Runtime.setSlice old 0 8 v).setWidth 8).getLsbD k = _
  rw [BitVec.getLsbD_setWidth, getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [hk]

theorem addR8R8Effect.read8 {p : BitVec 64} {dst src : BitVec 5} {s t : RamState}
    (h : (addR8R8Effect p dst src s).Holds s t) :
    (Operand.reg dst : Operand 8).read t =
      (Operand.reg dst : Operand 8).read s + (Operand.reg src : Operand 8).read s := by
  have hw := h.writes
  change (Operand.reg dst : Operand 64).read t = _ at hw
  change ((Operand.reg dst : Operand 64).read t).setWidth 8 = _
  rw [hw, mergeGPR8_setWidth]

attribute [x86_compose] addR8R8Effect

@[x86_local] theorem addR8R8Effect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (addR8R8Effect p dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [addR8R8Effect, h.read_reg]
  · cases i <;> simp_all [addR8R8Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [addR8R8Effect, Write.Full, Operand.Full]

end Md5.Proofs.Buffered.Update.Byte
