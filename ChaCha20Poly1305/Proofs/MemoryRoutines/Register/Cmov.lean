import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.Effect
import X86Proofs.Instructions.Branch.Cond
import X86Proofs.Step.Escape

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Register

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

theorem cmov64_operation {σ : Type} (s : X86.State σ) (dst src : BitVec 64)
    (cc : BitVec 4) :
    (X86.Instructions.Operations.CMOVcc 64 dst src cc).run s =
      (.ok (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then src else dst), s) := by
  unfold X86.Instructions.Operations.CMOVcc
  spec_run [Condition_Holds => conditionHolds_run _ _]
  cases condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;> rfl

theorem cmovb_r64_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVB_GPRv_GPRv ip ctx reg rm 0x42).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read s else dst.read s) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVB_GPRv_GPRv
  simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmov64_operation _ _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1Opcode42_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_42 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_42, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode42_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_42 ip ctx 0x42).run s =
      (X86.Instructions.CMOVB_GPRv_GPRv (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0x42).run t := by
  unfold Decode_Legacy_1_Opcode_42
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_42 ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1Opcode42_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_opcode42 [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x42, t)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_42 ip ctx 0x42).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem decodeLegacy1_run_of_rex_42_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0x42, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.CMOVB_GPRv_GPRv (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm) 0x42).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0x42, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0x42, afterFetches (beforeFetch s) 4) :=
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
  rw [decodeLegacy1_run_of_opcode42 _ _ _ _ rfl (hmode 4) f2,
    decodeLegacy1Opcode42_run_of_register _ _ _ _ _ hmod (hmode 5) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem cmovb_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0x42, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeResult t dst (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read t else dst.read t)
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_42_register s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmovb_r64_r64_form _ _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x42 [modrm] hrex.rexPrefix (by decide)
    hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmovb_r64_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t ↦
      writeResult t dst (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read t else dst.read t)
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeResult h 4 _ _ _

def cmovbR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if (StatusFlags.ofRFLAGS s.RFLAGS).CF then (Operand.reg src : Operand 64).read s
      else (Operand.reg dst : Operand 64).read s⟩] }

theorem cmovbR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (cmovbR64R64Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem cmovbR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (cmovbR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [cmovbR64R64Effect_components, Component.Covers]) code

theorem cmovb_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x0F, 0x42, modrm])
      (cmovbR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmovb_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), cmovb_r64_r64_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem cmovb_r8_rdx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x4C, 0x0F, 0x42, 0xC2])
      (cmovbR64R64Effect p 8 2) :=
  cmovb_r64_r64_effect_step p 0x4C 0xC2 (by unfold RexWPrefix; decide) (by decide)

theorem cmovb_rcx_r8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x49, 0x0F, 0x42, 0xC8])
      (cmovbR64R64Effect p 1 8) :=
  cmovb_r64_r64_effect_step p 0x49 0xC8 (by unfold RexWPrefix; decide) (by decide)

end ChaCha20Poly1305.Proofs.MemoryRoutines.Register
