import Md5.Proofs.MemoryRoutines.Register.Cmov
import Md5.Proofs.Block.Rounds.Register.Or

namespace Md5.Proofs.Streaming

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess
open Md5.Proofs.MemoryRoutines.Register Md5.Proofs.Block.Rounds.Register

theorem cmovae_r64_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVNB_GPRv_GPRv ip ctx reg rm 0x43).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if !(StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read s else dst.read s) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVNB_GPRv_GPRv
  simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmov64_operation _ _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1Opcode43_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_43 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_43, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode43_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_43 ip ctx 0x43).run s =
      (X86.Instructions.CMOVNB_GPRv_GPRv (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0x43).run t := by
  unfold Decode_Legacy_1_Opcode_43
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_43 ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1Opcode43_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_opcode43 [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x43, t)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_43 ip ctx 0x43).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem decodeLegacy1_run_of_rex_43_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0x43, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.CMOVNB_GPRv_GPRv (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm) 0x43).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0x43, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0x43, afterFetches (beforeFetch s) 4) :=
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
  rw [decodeLegacy1_run_of_opcode43 _ _ _ _ rfl (hmode 4) f2,
    decodeLegacy1Opcode43_run_of_register _ _ _ _ _ hmod (hmode 5) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem cmovae_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0x43, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeResult t dst (if !(StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read t else dst.read t)
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_43_register s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmovae_r64_r64_form _ _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x43 [modrm] hrex.rexPrefix (by decide)
    hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmovae_r64_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t ↦
      writeResult t dst (if !(StatusFlags.ofRFLAGS s.RFLAGS).CF then src.read t else dst.read t)
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeResult h 4 _ _ _

def cmovaeR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if !(StatusFlags.ofRFLAGS s.RFLAGS).CF then (Operand.reg src : Operand 64).read s
      else (Operand.reg dst : Operand 64).read s⟩] }

theorem cmovaeR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (cmovaeR64R64Effect p dst src s).components = [.reg dst, .rip] := rfl

theorem cmovaeR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (cmovaeR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [cmovaeR64R64Effect_components, Component.Covers]) code

theorem cmovae_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x0F, 0x43, modrm])
      (cmovaeR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmovae_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), cmovae_r64_r64_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem cmovae_rbp_rax_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0x0F, 0x43, 0xE8])
      (cmovaeR64R64Effect p 5 0) :=
  cmovae_r64_r64_effect_step p 0x48 0xE8 (by unfold RexWPrefix; decide) (by decide)

theorem writeGPR8_run_of_low {σ : Type} (s : X86.State σ) (r : BitVec 5)
    (hr : r.toNat < 4) (rex : Bool) (v : BitVec 8) (hmode : In64BitMode s) :
    (Write_GPR8 r rex v).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 v s.GPR[gprIndex r]) }) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ hmode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 4, r = BitVec.ofNat 5 i.val :=
    ⟨⟨r.toNat, hr⟩, by simp⟩
  clear hr
  finite_cases i <;> cases rex <;> rfl

theorem setcc_operation {σ : Type} (s : X86.State σ) (cc : BitVec 4) :
    (X86.Instructions.Operations.SETcc cc).run s =
      (.ok (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then 1 else 0), s) := by
  unfold X86.Instructions.Operations.SETcc
  spec_run [Condition_Holds => conditionHolds_run _ _]
  cases condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) <;> rfl

theorem setz_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false)
    (hr : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.SETZ_GPR8 ip ctx rm 0x94).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then 1 else 0) (dst.read s)) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SETZ_GPR8
  simp only [writeResult, Operand.write_reg64, Operand.read_reg64]
  spec_run [
    X86.Instructions.Operations.SETcc => setcc_operation _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ hr _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1Opcode94_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_94 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_94, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode94_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_94 ip ctx 0x94).run s =
      (X86.Instructions.SETZ_GPR8 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 0 3) 0x94).run t := by
  unfold Decode_Legacy_1_Opcode_94
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_94 ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1Opcode94_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_opcode94 [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x94, t)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_94 ip ctx 0x94).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem decodeLegacy1_run_of_94_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0F, 0x94, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SETZ_GPR8 (BitVec.add s.RIP 3#64)
        (legacyContext s.DS) (modrmRm modrm) 0x94).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0F, 0x94, modrm] := hcode
  have f1 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x94, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcode94 _ _ _ _ rfl (hmode 3) f1,
    decodeLegacy1Opcode94_run_of_register _ _ _ _ _ hmod (hmode 4) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem setz_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0F, 0x94, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeResult t dst
        (mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then 1 else 0) (dst.read t))
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_94_register s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [setz_r8_form (afterFetches (beforeFetch s) 4) (BitVec.add s.RIP 3#64)
    (legacyContext s.DS) (modrmRm modrm) hmode rfl hr] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x94 [modrm] (by decide)
    hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

def setzR8Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then 1 else 0)
        ((Operand.reg dst : Operand 64).read s)⟩] }

theorem setz_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, modrm])
      (setzR8Effect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, setz_r8_step s h modrm hmod hr hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem sete_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, 0xC0])
      (setzR8Effect p 0) := setz_r8_effect_step p 0xC0 (by decide) (by decide)

theorem sete_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x0F, 0x94, 0xC1])
      (setzR8Effect p 1) := setz_r8_effect_step p 0xC1 (by decide) (by decide)

theorem or_cl_al_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ds : Segment) (hmode : In64BitMode s) :
    (X86.Instructions.OR_GPR8_GPR8_08 ip (legacyContext ds) 0 1).run s =
      let dst : Operand 64 := .reg 1
      let out := orSpec (oracleBit s.oracle)
        ((Operand.reg 1 : Operand 8).read s) ((Operand.reg 0 : Operand 8).read s)
      (.ok (), writeOutputs s dst (mergeGPR 8 out.1 (dst.read s), out.2) 1 ip) := by
  unfold X86.Instructions.OR_GPR8_GPR8_08
  simp only [writeOutputs, Operand.write_reg64, Operand.read_reg64]
  spec_run [
    Read_GPR8 => readGPR8_run_of_low _ _ (by dsimp only [legacyContext]; decide) _ hmode,
    X86.Instructions.Operations.OR => or_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ _ (by dsimp only [legacyContext]; decide) _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0_run_of_opcode08 [Bindings]
    (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x08, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_08 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode08_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_08 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_08, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode08_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_08 ip context).run s =
      (X86.Instructions.OR_GPR8_GPR8_08 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_08
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode08_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_08 [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [0x08, modrm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.OR_GPR8_GPR8_08 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x08, modrm] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x08, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode08 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode08_run_of_register _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem or_cl_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x08, 0xC1]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t ↦
      let dst : Operand 64 := .reg 1
      let out := orSpec (oracleBit t.oracle)
        ((Operand.reg 1 : Operand 8).read t) ((Operand.reg 0 : Operand 8).read t)
      writeOutputs t dst (mergeGPR 8 out.1 (dst.read t), out.2) 1 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_08 s h 0xC1 (by decide) hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  change _ = some ((X86.Instructions.OR_GPR8_GPR8_08 _ (legacyContext s.DS) 0 1).run _)
    at hdecode
  rw [or_cl_al_form _ _ _ hmode] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x08 [0xC1]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def orClAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 1 : Operand 8).read s ||| (Operand.reg 0 : Operand 8).read s
  { rip := p + 2
    writes := [⟨(Operand.reg 1 : Operand 64),
      mergeGPR 8 r ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (andFlags r) }

theorem or_cl_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x08, 0xC1]) (orClAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, or_cl_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] orClAlEffect cmovaeR64R64Effect setzR8Effect

@[x86_local] theorem orClAlEffect_local (p : BitVec 64) : Effect.Local (orClAlEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [orClAlEffect, h.read_reg]
  · cases i <;> simp [orClAlEffect, Effect.flag, h.read_reg]
  · simp [orClAlEffect, Write.Full, Operand.Full]

def cmovaeR64R64FixedEffect (p : BitVec 64) (dst src : BitVec 5) (cf : Bool)
    (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if !cf then (Operand.reg src : Operand 64).read s
      else (Operand.reg dst : Operand 64).read s⟩] }

def setzR8FixedEffect (p : BitVec 64) (dst : BitVec 5) (zf : Bool) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (if zf then 1 else 0) ((Operand.reg dst : Operand 64).read s)⟩] }

attribute [x86_compose] cmovaeR64R64FixedEffect setzR8FixedEffect

@[x86_local] theorem cmovaeR64R64FixedEffect_local (p : BitVec 64) (dst src : BitVec 5)
    (cf : Bool) : Effect.Local (cmovaeR64R64FixedEffect p dst src cf) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [cmovaeR64R64FixedEffect, h.read_reg]
  · simpa only [cmovaeR64R64FixedEffect, Effect.flag] using congrArg some hi
  · simp [cmovaeR64R64FixedEffect, Write.Full, Operand.Full]

@[x86_local] theorem setzR8FixedEffect_local (p : BitVec 64) (dst : BitVec 5)
    (zf : Bool) : Effect.Local (setzR8FixedEffect p dst zf) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [setzR8FixedEffect, h.read_reg]
  · simpa only [setzR8FixedEffect, Effect.flag] using congrArg some hi
  · simp [setzR8FixedEffect, Write.Full, Operand.Full]

theorem cmovae_rbp_rax_fixed_effect_step [Bindings] (p : BitVec 64) (cf : Bool) :
    StepEffect (fun s ↦ s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = cf)
      (codeRange p [0x48, 0x0F, 0x43, 0xE8]) (cmovaeR64R64FixedEffect p 5 0 cf) := by
  rintro s h hcode ⟨hrip, hcf⟩
  obtain ⟨t, hstep, hready, heffect⟩ := cmovae_rbp_rax_effect_step p s h hcode hrip
  refine ⟨t, hstep, hready, ?_⟩
  simpa only [cmovaeR64R64Effect, cmovaeR64R64FixedEffect, hcf] using heffect

theorem setz_r8_fixed_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (zf : Bool)
    (hmod : modrmMod modrm = 3) (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s ↦ s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).ZF = zf)
      (codeRange p [0x0F, 0x94, modrm])
      (setzR8FixedEffect p (gprNumber 0 0 (modrmRm modrm)) zf) := by
  rintro s h hcode ⟨hrip, hzf⟩
  obtain ⟨t, hstep, hready, heffect⟩ := setz_r8_effect_step p modrm hmod hr s h hcode hrip
  refine ⟨t, hstep, hready, ?_⟩
  simpa only [setzR8Effect, setzR8FixedEffect, hzf] using heffect

theorem sete_al_fixed_effect_step [Bindings] (p : BitVec 64) (zf : Bool) :
    StepEffect (fun s ↦ s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).ZF = zf)
      (codeRange p [0x0F, 0x94, 0xC0]) (setzR8FixedEffect p 0 zf) :=
  setz_r8_fixed_effect_step p 0xC0 zf (by decide) (by decide)

theorem sete_cl_fixed_effect_step [Bindings] (p : BitVec 64) (zf : Bool) :
    StepEffect (fun s ↦ s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).ZF = zf)
      (codeRange p [0x0F, 0x94, 0xC1]) (setzR8FixedEffect p 1 zf) :=
  setz_r8_fixed_effect_step p 0xC1 zf (by decide) (by decide)

theorem setzR8Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (setzR8Effect p dst s).components = [.reg dst, .rip] := rfl

theorem setzR8Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (setzR8Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [setzR8Effect_components, Component.Covers]) code

theorem setzR8FixedEffect_components (p : BitVec 64) (dst : BitVec 5) (zf : Bool)
    (s : RamState) : (setzR8FixedEffect p dst zf s).components = [.reg dst, .rip] := rfl

theorem setzR8FixedEffect_avoids (p : BitVec 64) (dst : BitVec 5) (zf : Bool)
    (s : RamState) (code : CodeMap) : (setzR8FixedEffect p dst zf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [setzR8FixedEffect_components, Component.Covers]) code

theorem cmovaeR64R64FixedEffect_components (p : BitVec 64) (dst src : BitVec 5) (cf : Bool)
    (s : RamState) : (cmovaeR64R64FixedEffect p dst src cf s).components = [.reg dst, .rip] := rfl

theorem cmovaeR64R64FixedEffect_avoids (p : BitVec 64) (dst src : BitVec 5) (cf : Bool)
    (s : RamState) (code : CodeMap) : (cmovaeR64R64FixedEffect p dst src cf s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [cmovaeR64R64FixedEffect_components, Component.Covers]) code

theorem orClAlEffect_components (p : BitVec 64) (s : RamState) :
    (orClAlEffect p s).components = [.reg 1, .flags, .rip] := rfl

theorem orClAlEffect_avoids (p : BitVec 64) (s : RamState) (code : CodeMap) :
    (orClAlEffect p s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [orClAlEffect_components, Component.Covers]) code

end Md5.Proofs.Streaming
