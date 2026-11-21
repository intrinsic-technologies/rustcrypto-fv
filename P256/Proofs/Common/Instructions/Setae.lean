import P256.Proofs.Common.Instructions.Setb.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions.Setb

theorem decodeLegacy1_run_of_setaeOpcode [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (opcode : UInt8) (hop : opcode = 0x93)
    (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok opcode.toBitVec, t)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_92 ip context opcode.toBitVec).run t) := by
  subst opcode
  all_goals
    unfold Decode_Legacy_1
    rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
    rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
    repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
    repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
    rfl

theorem decodeLegacy1_run_of_setae [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm opcode : UInt8) (hop : opcode = 0x93)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hopbyte : bytes[k]? = some opcode) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.SETB_GPR8 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmRm modrm) opcode.toBitVec).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok opcode.toBitVec, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = opcode from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hopbyte)] at this
    exact this
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64) 8).run
      (afterFetches (beforeFetch s) (k + 2)) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) (k + 3)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 2) hf hc hlow (k + 1) hlen hk
    rw [show bytes[k + 1] = modrm from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hm)] at this
    rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 1)) from add_ofNat_add s.RIP k 1]
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_setaeOpcode _ _ _ _ opcode hop hrex2 (hmode _) f1,
    decodeLegacy1Opcode92_run_of_register _ _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl
theorem setae_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex opcode modrm : UInt8) (hrex : RexPrefix rex.toBitVec)
    (hop : opcode = 0x93) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, opcode, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) t) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_setae s h (rexContext s.DS rex.toBitVec) rfl
    modrm opcode hop hmod _ 2 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [setb_r_form _ _ _ _ _ hmode rfl (.inl rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex opcode [modrm] hrex
    (by subst opcode <;> decide) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem setae_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex opcode modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : opcode = 0x93) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, opcode, modrm])
      (setccR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (opcode.toBitVec.extractLsb' 0 4)) := by
  rintro s h hcode rfl
  refine ⟨_, setae_r8_rex_step s h rex opcode modrm hrex hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [writeResult, Operand.write, Operand.read_reg64, Fin.getElem_fin, Vector.getElem_set_self]
  rfl


end P256.Proofs.Common.Instructions
