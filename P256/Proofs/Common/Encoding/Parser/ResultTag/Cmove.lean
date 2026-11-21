import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmovR32R32Effect cmovR32R32Value cmov_r32_r32_form decodeLegacy1Opcode42_run_of_register)

namespace P256.Proofs.Common.Encoding.Parser.ResultTag

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy1_run_of_cmove [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode u) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x44, u)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_42 ip ctx 0x44).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem cmove_r32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0f, 0x44, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst := gprNumber 0 0 (modrmReg modrm)
    let src := gprNumber 0 0 (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg dst)
        (cmovR32R32Value 4 dst src t) (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0f, 0x44, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64
      from BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_cmove _ _ (BitVec.add s.RIP 1#64)
    (legacyContext s.DS) rfl (hmode 3) f1
  rw [decodeLegacy1Opcode42_run_of_register _ _ _ _ _ _ hmod (hmode 4) hf f2,
    cmov_r32_r32_form _ _ _ _ _ _ (hmode 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x44 [modrm]
    (by decide) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem cmove_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0x44, modrm])
      (cmovR32R32Effect p 4
        (gprNumber 0 0 (modrmReg modrm)) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmove_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  simp only [cmovR32R32Value, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

end P256.Proofs.Common.Encoding.Parser.ResultTag
