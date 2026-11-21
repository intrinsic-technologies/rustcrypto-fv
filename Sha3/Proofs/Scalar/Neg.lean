import X86Proofs.Instructions.Sub.Operation
import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import Sha3.Proofs.X86.Instructions.Not.Decode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem subtract32_run (x y : BitVec 32) :
    Subtract (size := 32) x y =
      let (r, f) := subSpec x y
      .ok (r, BitVec.ofBool f.CF, BitVec.ofBool f.OF, BitVec.ofBool f.AF) := by
  simp only [Subtract, bind, Except.bind, Int.zero_le_ofNat, decide_true, assert_of_true,
    pure, Except.pure, Runtime.CheckedSlice.read, Runtime.intSlice, Std.le_refl, Bool.and_self,
    Int.reduceToNat, unsigned_eq, Int.toNat_one, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    Nat.pow_one, Nat.zero_mod, Int.cast_ofNat_Int, Int.add_zero, Int.toNat_zero, Int.pow_zero,
    Int.ediv_one, ofInt_sub_toNat, Runtime.sliceInclusive, Int.reduceSub, Int.reduceAdd,
    Int.zero_add, Int.reduceLE, slice_eq_pure, Int.sub_zero, Nat.reduceLeDiff, ofInt4_sub_toNat,
    beq_iff_eq, toNat_sub_eq_iff, Nat.not_lt, signed_eq, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.reducePow, Int.natCast_emod, toNat_sub_mod16_eq_iff,
    subSpec, ne_eq, decide_not, Except.ok.injEq, Prod.mk.injEq, true_and]
  rw [ite_zero_one, ite_zero_one, ite_zero_one]
  simp only [← Nat.not_le, decide_not, and_self]

theorem neg32_operation {σ : Type} (s : X86.State σ) (x : BitVec 32) :
    (X86.Instructions.Operations.NEG 32 x).run s =
      let (r, flags) := subSpec 0 x
      (.ok r, setFlags s flags) := by
  unfold X86.Instructions.Operations.NEG
  simp only [stdZero_eq_pure (by decide : (0 : Int) ≤ 32), pure_bind, subtract32_run,
    isParityEven8_run]
  repeat spec_bind_rfl
  simp only [subSpec, BitVec.ofNat_eq_ofNat, Int.reduceToNat, BitVec.zero_sub,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, BitVec.extractLsb'_zero,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero, beq_zero_eq_decide, BitVec.neg_eq_zero_iff,
    BitVec.toInt_zero, Int.zero_sub, ne_eq, decide_not, Int.reduceSub, Int.toNat_one,
    Nat.reduceAdd, extractLsb'_msb, decide_eq_true_eq, Int.toNat_zero, specM_pure_run,
    setFlags, StatusFlags.store]
  congr 2
  rw [ite_one_zero, ite_one_zero, ite_zero_one]
  simp only [Bool.decide_eq_true]
  congr 1
  apply congrArg BitVec.ofBool
  simp [BitVec.toNat_eq, Nat.pos_iff_ne_zero]

theorem decodeLegacy0_run_of_F7_neg [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [0xF7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.NEG_GPRv (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF7, modrm] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xF7, afterFetches (beforeFetch s) 2) := by
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
  rw [decodeLegacy0_run_of_opcodeF7 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0OpcodeF7_run_of_neg_register _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

theorem neg_r32_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NEG_GPRv ip ctx rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (subSpec 0 (dst.read s)) 0 ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.NEG_GPRv
  simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
  spec_run [
    Read_GPR => readGPR32_run _ _ hmode,
    X86.Instructions.Operations.NEG => neg32_operation _ _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem neg_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [0xF7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F7_neg s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r32_form _ _ _ _ hmode (legacyContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF7 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem neg_r32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ _ _

def negR32Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + 2
    writes := [⟨(Operand.reg dst : Operand 64), (-a).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

abbrev negEcxEffect (p : BitVec 64) : RamState → Effect := negR32Effect p 1

theorem negR32Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (negR32Effect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem neg_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0xF7, modrm])
      (negR32Effect p (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ _ _, ?_, StatusFlagsOutcome.allows_store
      (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact congrArg (BitVec.setWidth 64) (BitVec.zero_sub _)

theorem neg_ecx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0xF7, 0xD9]) (negEcxEffect p) :=
  neg_r32_effect_step p 0xD9 (by decide +kernel) (by decide +kernel)

end X86Proofs
