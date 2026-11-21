import P256.Proofs.Common.Instructions.CmovMemory.Effect

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions

theorem decodeLegacy1_run_of_cmovaeMemoryOpcode [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode u) (op : UInt8) (hop : op = 0x43)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_42 ip ctx op.toBitVec).run u) := by
  subst op
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem decodeLegacy1_run_of_cmovae_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (op : UInt8) (hop : op = 0x43) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hopcode : bytes[k]? = some op) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CMOVB_GPRv_MEMv (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm) op.toBitVec).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm
      cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok op.toBitVec, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = op from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hopcode)] at this
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
  rw [decodeLegacy1_run_of_cmovaeMemoryOpcode _ _ _ _ hrex2 (hmode _) op hop f1,
    decodeLegacy1Opcode42_run_of_memory _ _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl
theorem cmovae32_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (op : UInt8) (hop : op = 0x43)
    (hsize : ctx.operand_size = 32) (haddr64 : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext ctx am) (bytes : List UInt8) (k : Nat) (hk : k ≤ 2)
    (hopcode : bytes[k]? = some op) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hlen : bytes.length = k + 2 + am.tail.length)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) 4) :
    let dst := gprNumber ctx.rex_r4 ctx.rex_r3 reg
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (bytes.length + 1)) "load")
        (.reg dst : Operand 32)
        (cmovR32M32Value (op.toBitVec.extractLsb' 0 4) dst
          (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_cmovae_memory s h ctx hrex2 op hop (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    bytes k (by omega) hopcode hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = bytes.length + 1 by omega,
    show k + 2 + am.tail.length = bytes.length by omega] at hea
  let t := afterFetches (beforeFetch s) (bytes.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) =
      am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))
  rw [haddr] at hrip
  replace hea : (Effective_Address 64 ctx am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 bytes.length), am.isRip, am.baseUsesRsp), t) := hea
  rw [cmov_r32_m32_form _ t _ _ _ _ _ _ hsize haddr64 hlock _ _ _ _ _ hea hrip ht hmode
    (hread.of_external_eq rfl)] at hdecode
  exact hdecode

theorem cmovae_r32_m32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (op : UInt8) (hop : op = 0x43) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0f :: op :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))
      4) :
    let dst := gprNumber 0 0 reg
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") (.reg dst : Operand 32)
        (cmovR32M32Value (op.toBitVec.extractLsb' 0 4) dst
          (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))) s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlen : (0x0f :: op :: am.modrm reg :: am.tail : List UInt8).length =
      3 + am.tail.length := by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat + (0x0f :: op :: am.modrm reg :: am.tail : List UInt8).length ≤ 2^32 :=
    by rw [hlen]; exact hlow
  have hdecode := cmovae32_memory_run s h (legacyContext s.DS) rfl op hop rfl rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb) _ 1 (by decide) rfl rfl
    (fun j _ => by rw [show 1 + 2 + j = j + 1 + 1 + 1 by omega]; rfl)
    (by simp only [List.length_cons]; omega) hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h op _ (by subst op <;> decide)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem cmovae_r32_m32_effect_step [Bindings] (p : BitVec 64)
    (op : UInt8) (hop : op = 0x43)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0f :: op :: am.modrm reg :: am.tail))
      (cmovR32M32Effect p (3 + am.tail.length) (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, cmovae_r32_m32_step s h op hop reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  rfl


end P256.Proofs.Common.Instructions
