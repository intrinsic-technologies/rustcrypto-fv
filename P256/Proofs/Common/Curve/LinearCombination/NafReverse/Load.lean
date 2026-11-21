import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Common.Curve.LinearCombination.NafReverse

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem selectLegacy1OpcodeB7_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hosz : context.osz_prefix_present = false) (hrew : context.rex_w = 0) :
    Select_Legacy_1_Opcode_B7 context true a b c d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_B7, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, hrew, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB7_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hosz : context.osz_prefix_present = false) (hrew : context.rex_w = 0) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B7 ip context).run s =
      (X86.Instructions.MOVZX_GPR32_MEMw_0 (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B7
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_B7 context mode a b c d e f modrm) _ 2 hmode hf
    (fun a b c d e f => selectLegacy1OpcodeB7_run_of_memory context a b c d e f modrm hmod hosz hrew)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_B7_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrew : ctx.rex_w = 0) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hb7 : bytes[k]? = some 0xB7) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOVZX_GPR32_MEMw_0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) = (.ok 0xB7, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0xB7 from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hb7)] at this
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
  rw [decodeLegacy1_run_of_opcodeB7 _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1OpcodeB7_run_of_memory _ _ _ _ _ hosz hrew hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem movzx16_operation_except (n : Nat) (hn : n = 64 ∨ n = 32) (x : BitVec 16) :
    X86.Instructions.Operations.MOVZX 16 n x = .ok (movzxSpec n x) := by
  rcases hn with rfl | rfl <;>
  simp [X86.Instructions.Operations.MOVZX, x86_runtime, movzxSpec, bind, pure, Except.bind,
    Except.pure]

theorem movzx16_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32)
    (x : BitVec 16) :
    (liftM (X86.Instructions.Operations.MOVZX 16 n x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movzxSpec n x), s) := by
  rw [movzx16_operation_except n hn]
  rfl

theorem movzx_r_m16_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrew : ctx.rex_w = 0)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : addr.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVZX_GPR32_MEMw_0 ip ctx mod reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movzxSpec 32 ((Operand.mem addr : Operand 16).read t)) next) := by
  have hread := logicalMemRead_run t ht isStack addr 16 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  have hcontext :
      {ctx with address_size := 64, lock_prefix_present := false, osz_prefix_present := false, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPR32_MEMw_0
  simp only [writeResult, Operand.write_reg32]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  refine (specM_bind_run _ _ hread).trans ?_
  spec_bind_rfl
  refine (specM_bind_run _ _ (movzx16_operation _ 32 (.inr rfl) _)).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  rw [writeGPR32_run _ _ _ ?hm]
  all_goals first | exact hmode.of_cs_lma_eq rfl rfl | rfl

theorem movzx_0FB7_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrew : ctx.rex_w = 0) (haddr64 : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext ctx am) (bytes : List UInt8) (k : Nat) (hk : k ≤ 2)
    (hb7 : bytes[k]? = some 0xB7) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hlen : bytes.length = k + 2 + am.tail.length)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) 2) :
    let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (bytes.length + 1)) "load")
        dst (movzxSpec 32 ((Operand.mem (am.addr s (BitVec.add s.RIP
          (BitVec.ofNat 64 bytes.length))) : Operand 16).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_B7_memory s h ctx hrex2 hosz hrew (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) hb7 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = bytes.length + 1 by omega,
    show k + 2 + am.tail.length = bytes.length by omega] at hea
  let t := afterFetches (beforeFetch s) (bytes.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  rw [movzx_r_m16_form _ t _ _ _ _ _ haddr64 hlock hosz hrew _ _ _ _ _ hea hrip ht hmode
    hread.low hread.mem] at hdecode
  exact hdecode

theorem movzx_r32_m16_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: 0xB7 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))
      2) :
    let dst : Operand 32 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec 32 ((Operand.mem (am.addr s (BitVec.add s.RIP
          (BitVec.ofNat 64 (3 + am.tail.length)))) : Operand 16).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlen : (0x0F :: 0xB7 :: am.modrm reg :: am.tail : List UInt8).length = 3 + am.tail.length :=
    by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat + (0x0F :: 0xB7 :: am.modrm reg :: am.tail : List UInt8).length ≤ 2^32 :=
    by rw [hlen]; exact hlow
  have hctx : AddrContext (legacyContext s.DS) am := ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩
  have hdecode := movzx_0FB7_memory_run s h (legacyContext s.DS) rfl rfl rfl rfl rfl
    reg am hv hctx _ 1 (by decide) rfl rfl
    (fun j _ => by rw [show 1 + 2 + j = j + 1 + 1 + 1 by omega]; rfl) (by simp only [List.length_cons]; omega)
    hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xB7 _ ⟨by decide, by decide⟩ hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def movzxR32M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s).setWidth 64⟩] }

theorem movzx_r32_m16_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x0F :: 0xB7 :: am.modrm reg :: am.tail))
      (movzxR32M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    subst hp
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  subst hp
  refine ⟨_, movzx_r32_m16_step s h reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec]
  exact BitVec.setWidth_setWidth (by decide)

@[x86_local] theorem movzxR32M16Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) : Effect.Local (movzxR32M16Effect p len dst am) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movzxR32M16Effect, AddrMode.addr_obs h, h.read_mem]
  · intro s
    simp [movzxR32M16Effect, Write.Full, Operand.Full]

attribute [x86_compose] movzxR32M16Effect

end P256.Proofs.Common.Curve.LinearCombination.NafReverse
