import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Common.EffectCompose.Conditions

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Setb (decodeLegacy1Opcode92_run_of_memory decodeLegacy1Opcode92_run_of_register setb_r_form setccM8Effect setccR8Effect setccValue setcc_m8_form)

namespace P256.Proofs.Common.Instructions.Setcc

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

@[x86_local_on] theorem setccM8Effect_localOn_3
    (p : BitVec 64) (len : Nat) (am : AddrMode) {cc : BitVec 4} (hcc : cc = 3) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.CF] (setccM8Effect p len am cc) := by
  subst cc
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).CF := hf .CF (by simp)
    simp [setccM8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs ho, setccValue, condHolds, hc]
  · intro t
    simp [setccM8Effect, storeEffect, Write.Full, Operand.Full]

@[x86_local_on] theorem setccR8Effect_localOn_5
    (p : BitVec 64) (len : Nat) (dst : BitVec 5) {cc : BitVec 4} (hcc : cc = 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.ZF] (setccR8Effect p len dst cc) := by
  subst cc
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).ZF := hf .ZF (by simp)
    simp [setccR8Effect, setccValue, condHolds, ho.gpr, hc]
  · intro t
    simp [setccR8Effect, Write.Full, Operand.Full]

@[x86_local_on] theorem setccM8Effect_localOn_5
    (p : BitVec 64) (len : Nat) (am : AddrMode) {cc : BitVec 4} (hcc : cc = 5) :
    P256.Proofs.Common.EffectCompose.Effect.LocalOn [.ZF] (setccM8Effect p len am cc) := by
  subst cc
  apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro t t' ho hf
    have hc : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        (StatusFlags.ofRFLAGS t'.RFLAGS).ZF := hf .ZF (by simp)
    simp [setccM8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs ho, setccValue, condHolds, hc]
  · intro t
    simp [setccM8Effect, storeEffect, Write.Full, Operand.Full]

def ExtraOpcode (opcode : UInt8) : Prop := opcode = 0x93 ∨ opcode = 0x95

theorem decodeLegacy1_run_of_setccExtraOpcode [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (opcode : UInt8) (hop : ExtraOpcode opcode)
    (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok opcode.toBitVec, t)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_92 ip context opcode.toBitVec).run t) := by
  rcases hop with rfl | rfl
  all_goals
    unfold Decode_Legacy_1
    rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
    rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
    repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
    repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
    rfl

theorem decodeLegacy1_run_of_setccExtra [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm opcode : UInt8) (hop : ExtraOpcode opcode)
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
  rw [decodeLegacy1_run_of_setccExtraOpcode _ _ _ _ opcode hop hrex2 (hmode _) f1,
    decodeLegacy1Opcode92_run_of_register _ _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem setccExtra_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex opcode modrm : UInt8) (hrex : RexPrefix rex.toBitVec)
    (hop : ExtraOpcode opcode) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, opcode, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) t) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_setccExtra s h (rexContext s.DS rex.toBitVec) rfl
    modrm opcode hop hmod _ 2 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [setb_r_form _ _ _ _ _ hmode rfl (.inl rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex opcode [modrm] hrex
    (by rcases hop with rfl | rfl <;> decide) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem setccExtra_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex opcode modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : ExtraOpcode opcode) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, opcode, modrm])
      (setccR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (opcode.toBitVec.extractLsb' 0 4)) := by
  rintro s h hcode rfl
  refine ⟨_, setccExtra_r8_rex_step s h rex opcode modrm hrex hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [writeResult, Operand.write, Operand.read_reg64, Fin.getElem_fin, Vector.getElem_set_self]
  rfl

theorem decodeLegacy1_run_of_setccExtra_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm opcode : UInt8) (hop : ExtraOpcode opcode)
    (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hopbyte : bytes[k]? = some opcode) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.SETB_MEMb (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmRm modrm) opcode.toBitVec).run
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
  rw [decodeLegacy1_run_of_setccExtraOpcode _ _ _ _ opcode hop hrex2 (hmode _) f1,
    decodeLegacy1Opcode92_run_of_memory _ _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem setccExtra_m8_scan_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (opcode : UInt8) (hop : ExtraOpcode opcode)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (pre.length + 3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store")
        (.mem (am.addrAt s (pre.length + 3 + am.tail.length)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  have h5 := am.tail_length_le
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons]; omega
  have hdecode := decodeLegacy1_run_of_setccExtra_memory s h (scanContext s.DS (PrefixSegments.ofState s) pre) hrex2
    (am.modrm reg) opcode hop (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    _ (pre.length + 1) (by omega)
    (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; rfl)
    (by rw [List.getElem?_append_right (by omega)];
        rw [show pre.length + 1 + 1 - pre.length = 2 by omega]; rfl) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x0F :: opcode :: am.modrm reg :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) (pre.length + 4) h.fetchReady h.cpu.ds h.cpu.ss
    am hv (scanContext s.DS (PrefixSegments.ofState s) pre) hctx hc hlow' (pre.length + 3)
    (fun j _ => by
      rw [List.getElem?_append_right (by omega)]
      rw [show pre.length + 3 + j - pre.length = 3 + j by omega]
      exact getElem?_cons3 _ _ _ _ j)
    (by simp; omega) (by omega)
  rw [show pre.length + 4 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  have headdr : am.addr (beforeFetch s)
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))) =
      am.addrAt s (pre.length + 3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  rw [headdr] at hrip
  rw [show pre.length + 1 + 2 = pre.length + 3 by omega,
    show pre.length + 1 + 3 = pre.length + 4 by omega,
    setcc_m8_form _ t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
      _ _ _ opcode.toBitVec haddr hlock _ _ _ _ _ hea hrip ht
      (hw.of_external_eq rfl)] at hdecode
  rw [show pre.length + 1 + 1 = pre.length + 2 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre opcode _ hpre
    (by rcases hop with rfl | rfl <;> decide) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem setccExtra_m8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (opcode : UInt8) (hop : ExtraOpcode opcode) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: opcode :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (setccValue (opcode.toBitVec.extractLsb' 0 4) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  setccExtra_m8_scan_step s h [] (by simp) (by decide) opcode hop rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) hcode hlow hw

theorem setccExtra_m8_effect_step [Bindings] (p : BitVec 64) (opcode : UInt8)
    (hop : ExtraOpcode opcode) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0x0F :: opcode :: am.modrm reg :: am.tail))
      (setccM8Effect p (3 + am.tail.length) am (opcode.toBitVec.extractLsb' 0 4)) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact setccExtra_m8_step s h opcode hop reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

end P256.Proofs.Common.Instructions.Setcc
