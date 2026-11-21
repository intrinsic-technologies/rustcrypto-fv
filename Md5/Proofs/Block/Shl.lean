import X86Proofs.Core.Shift
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

namespace Md5.Proofs.Block

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shlSpec {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat)
    (x : BitVec n) : BitVec n × StatusFlags :=
  let r := x <<< c
  let cf := (x <<< (c - 1)).msb
  (r, if c = 0 then old else
    { CF := cf, PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then r.msb ^^ cf else of })

def shlFlags {n : Nat} (old : StatusFlags) (c : Nat) (x : BitVec n) :
    StatusFlagsOutcome :=
  let r := x <<< c
  let cf := (x <<< (c - 1)).msb
  if c = 0 then .ofStatusFlags old else
    { CF := some cf, PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb,
      OF := if c = 1 then some (r.msb ^^ cf) else none }

theorem shlFlags_allows {n : Nat} (old : StatusFlags) (of af : Bool) (c : Nat)
    (x : BitVec n) : (shlFlags old c x).Allows (shlSpec old of af c x).2 := by
  unfold shlFlags shlSpec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

def shlLoopStep {n : Nat} (acc : BitVec n × BitVec 1) : BitVec n × BitVec 1 :=
  (acc.1 <<< 1, acc.1.extractLsb' (n - 1) 1)

theorem shl_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat) (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
      (fun (acc : BitVec n × BitVec 1) (_ : Int) =>
        (acc.1 <<< 1, acc.1.extractLsb' (n - 1) 1)) (x, cf) =
      (x <<< k, (x <<< (k - 1)).extractLsb' (n - 1) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) =
      (List.range k).map (fun i : Nat ↦ (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel, Prod.mk.injEq]
    exact ⟨(BitVec.shiftLeft_add x (k + 1) 1).symm, trivial⟩

theorem shl_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.SHL n x count).run s =
      let c := shiftCount n count
      let (r, flags) := shlSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (shrOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (shrOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h ↦ by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h ↦ by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [shlSpec, shrOracleBits, shrOracleAF]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SHL
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceBEq, Bool.false_eq_true, ↓reduceIte,
      Int.reduceToNat, unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    by_cases h0 : c = 0
    · subst h0
      simp
    have e0 : ((c : Int) != 0) = true := by simp; omega
    simp only [e0, h0, ↓reduceIte]
    spec_bind_rfl
    refine (specM_bind_run _ _ (specM_forIn_run _ _
      (fun _ (acc : BitVec _ × BitVec 1) =>
        shlLoopStep acc) _ _ ?_)).trans ?_
    · intro _ _ _
      rfl
    simp only [shlLoopStep]
    rw [shl_fold _ _ _ (by omega)]
    generalize x <<< c = r
    by_cases h1 : c = 1
    · subst h1
      simp only [↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · have e1 : ((c : Int) == 1) = false := by simp; omega
      simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

theorem shl_r_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPRv_IMMb_C1r4 ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount n count
      (.ok (), writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read s)) (shrOracleBits c)
        (BitVec.add ip 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHL_GPRv_IMMb_C1r4
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHL => shl_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHL_GPRv_IMMb_C1r4
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHL => shl_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0OpcodeC1_run_of_shl_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_C1 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_C1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeC1_run_of_shl_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_C1 ip context).run s =
      (X86.Instructions.SHL_GPRv_IMMb_C1r4 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_C1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0OpcodeC1_run_of_shl_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_C1_shl [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SHL_GPRv_IMMb_C1r4 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0xC1, modrm, imm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xC1, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeC1 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeC1_run_of_shl_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem shl_r64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_shl s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [shl_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) 64 (by decide)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem shl_r64_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

def shlR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem shlR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (shlR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (shlR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [shlR64Effect_components, Component.Covers]) code

theorem shl_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (shlR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (shlR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => shlR64Effect_avoids p _ _ _ s _)
    (shl_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem shl_rax_six_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0xc1, 0xe0, 0x06])
      (shlR64Effect p 4 0 6) :=
  shl_r64_imm8_effect_step p 0x48 0xe0 0x06 (by unfold RexWPrefix; decide)
    (by decide) (by decide)

theorem shl_rax_six_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x48, 0xc1, 0xe0, 0x06])
      (Effect.post (shlR64Effect p 4 0 6)) :=
  Triple.of_effect (fun s _ ↦ shlR64Effect_avoids p 4 0 6 s _)
    (shl_rax_six_effect_step p)

attribute [x86_compose] shlR64Effect shlFlags

@[x86_local] theorem shlR64Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {c : Nat} : Effect.Local (shlR64Effect p len dst c) := by
  refine ⟨fun t t' h ↦ ?_, fun t t' h ↦ ?_, fun t t' h ↦ ?_,
    fun t t' h i hi ↦ ?_, fun t ↦ ?_⟩
  · rfl
  · simp only [shlR64Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [shlR64Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, shlFlags, h.read_reg] <;>
      split <;> simp_all
  · simp [shlR64Effect, Write.Full, Operand.Full]

end Md5.Proofs.Block
