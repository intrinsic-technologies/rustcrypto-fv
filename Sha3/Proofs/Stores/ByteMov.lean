import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.X86.Instructions.MemAlu.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode88_run_of_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_88 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_0_Opcode_88, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode88_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_88 ip context).run s =
      (X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_88
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦ selectLegacy0Opcode88_run_of_memory context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_opcode88_memory [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x88, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_88 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0_run_of_88_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8)
    (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x88)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x88 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode ↦ decodeLegacy0_run_of_opcode88_memory a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe ↦ decodeLegacy0Opcode88_run_of_memory a u _ ctx _ hmod hmode hfe hf)

theorem mov_m8_r8_form_of_readable [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (off next addr : BitVec 64) (isStack isRip : Bool)
    {baseUsesRsp : Bool} (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : MemReadable t addr 1) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand 8)
        (movSpec (src.read t)) next) := by
  have hwrite := Sha3.Proofs.logicalMemWrite_run_any _ (ht.withNextIP next) isStack addr 8
    (by decide) ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t)
    hw.low hw.mem
  rcases hreg with hrex | hlow4
  · have hcontext :
        {ctx with
          address_size := 64, lock_prefix_present := false, rex_prefix_present := true} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_MEMb_GPR8_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR8_run_of_rex _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext : {ctx with address_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_MEMb_GPR8_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR8_run_of_low _ _ hlow4 _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

theorem mov_m8_r8_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        reg).toNat < 4)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x88 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := am.addrAt s (pre.length + 2 + am.tail.length)
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2 + am.tail.length) fun t ↦
      writeResult (dataAccess t "store") (.mem addr : Operand 8) (movSpec (src.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))))) := by
  intro ctx addr src
  have hlen' : (pre ++ 0x88 :: am.modrm reg :: am.tail).length =
      pre.length + 2 + am.tail.length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x88 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_88_memory s h _ pre.length (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow' (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) ctx hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x88 reg am hv [] ctx hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [mov_m8_r8_form_of_readable _ t _ _ _ _ _ haddr hlock hreg _ _ _ _ _ hea hrip
    (memAlu_dataReady h _) hmode (hread.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x88 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mov_m8_r8_effect_step_of_readable [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePreReadable p (storeAddrAt p am (2 + am.tail.length)) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
        fun s ↦ (Operand.reg (gprNumber 0 0 reg) : Operand 8).read s) := by
  refine StepEffect.of_store_readable (n := 8) (by decide) (by decide) _ _
    (fun _ h ↦ h.2) ?_
  intro s hready hcode hpre
  obtain ⟨⟨hp, hw⟩, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  exact mov_m8_r8_step_of_readable s hready [] (by simp) (by simp) rfl rfl rfl reg
    (.inr (gprNumber_low4 reg hreg)) am hv (AddrContext.legacy _ am hx hb) hcode.bytesAt
    (hcode.low_len
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_nil]; omega)
      (by simp only [List.length_nil]; omega)) hw

theorem mov_m8_r8_rex_effect_step_of_readable [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (storeEffect p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length))
        fun s ↦ (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 8).read s) := by
  refine StepEffect.of_store_readable (n := 8) (by decide) (by decide) _ _
    (fun _ h ↦ h.2) ?_
  intro s hready hcode hpre
  obtain ⟨⟨hp, hw⟩, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have hstep := mov_m8_r8_step_of_readable s hready [rex] (by simpa using hr.scanPrefix)
    (by simp) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    reg (.inl (by rw [scanContext_rex _ _ hr]; rfl)) am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt
    (hcode.low_len
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)) hw
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

end X86Proofs
