import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr
import X86Proofs.Step.Decode.Legacy0Opcode83
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Triple
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Epilogue.Return
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Effect
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Interface

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Base16ct.Proofs.Base16ctUpperEncodeCorrect.Epilogue (restore_return)

theorem selectLegacy0Opcode83_run_of_r7_memory (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_83 context true a b c d e f modrm = .ok 17 := by
  simp [Select_Legacy_0_Opcode_83, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode83_run_of_r7_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_83 ip context).run s =
      (X86.Instructions.CMP_MEMv_IMMb (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_83
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode83_run_of_r7_memory context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_83_r7_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 7) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x83)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CMP_MEMv_IMMb (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x83 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode83 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0Opcode83_run_of_r7_memory a u _ ctx _ hmod hreg hmode hfe hf)

theorem cmp_m64_imm8_form [Bindings] (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64) = .ok addr)
    (hu : DataReady u) (hlow : addr.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (u.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMP_MEMv_IMMb ip ctx mod rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess u "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read u) (imm.signExtend 64)) 0
        (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run u hu isStack addr 64 (by decide) .Memory_Read (.inl rfl)
    hlow hmem
  have hcontext :
      {ctx with operand_size := 64, address_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_MEMv_IMMb
  simp only [writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address 64 isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.CMP => cmp_operation _ 64 (by decide) _ _]

theorem cmp_m64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (imm : UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 3 + am.tail.length)) 8) :
    let addr := am.addrAt s (pre.length + 3 + am.tail.length)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeFlagsOutputs (dataAccess t "load")
        (cmpSpec ((Operand.mem addr : Operand 64).read t) (imm.toBitVec.signExtend 64)) 0
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have hlen' : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])).length =
      pre.length + 3 + am.tail.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hlow' : s.RIP.toNat + (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_83_r7_memory s h _ pre.length (am.modrm 7)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _)
    (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea s h pre 0x83 7 am hv [imm] _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm])) := hcode
  have hfetch := memFetch_run_of_bytesAt (beforeFetch s)
    (pre.length + 3 + am.tail.length) h.fetchReady hc
    hlow' (pre.length + 2 + am.tail.length) (by rw [hlen']; omega) (by omega)
  have himm : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]'
      (by rw [hlen']; omega) = imm := by
    have : (pre ++ 0x83 :: am.modrm 7 :: (am.tail ++ [imm]))[pre.length + 2 + am.tail.length]? =
        some imm := by rw [getElem?_pre_tail]; simp
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
  rw [himm] at hfetch
  let u := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl,
    show pre.length + 3 + am.tail.length = pre.length + 2 + am.tail.length + 1 by omega,
    ← add_tail_imm] at hrip
  rw [cmp_m64_imm8_form _ _ u _ _ _ _ haddr hsize hlock _ _ _ _ _ _ hea hfetch hrip
    (memAlu_dataReady h _)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.low)
    (by rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega]; exact hread.mem)] at hdecode
  rw [add_tail_imm, ← show pre.length + 3 + am.tail.length =
      pre.length + 2 + am.tail.length + 1 by omega] at hdecode
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0x83 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

def cmpM64Imm8Effect (p : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (4 + am.tail.length)
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s)
      (imm.signExtend 64))) }

theorem cmp_m64_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x48 :: 0x83 :: am.modrm 7 :: (am.tail ++ [imm])))
      (cmpM64Imm8Effect p am imm.toBitVec) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := cmp_m64_imm8_step s h [0x48] (by simp [ScanPrefix, RexPrefix])
    (by decide) rfl rfl rfl rfl am hv
    (AddrContext.rex _ _ am hx.symm hb.symm) imm hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem lowerEncodeAbiBranch [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100156) (hRead : MemReadable s (stackPtr s) 8)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.mem (stackPtr s) : Operand 64).read s = 0 then
        0x10016d else 0x10015d) ∧ AgreesExcept [.flags, .rip] s t := by
  have hc : CodeIn (codeRange 0x100156 [0x48, 0x83, 0x3c, 0x24, 0]) s :=
    program_text_slice hCode 0x156 5 (by decide +kernel)
  have haddr (v : RamState) (next : BitVec 64) :
      (AddrMode.sib 4 none 0 .none).addr v next = stackPtr v := by
    change stackPtr v + 0#64 = stackPtr v
    exact BitVec.add_zero _
  have hp : LoadPre 0x100156
      (fun t => (AddrMode.sib 4 none 0 (.none)).addr t (0x100156 + 5)) 8 s := by
    refine ⟨hRip, ?_⟩
    rw [haddr]
    exact hRead
  obtain ⟨u, ha, hu, he⟩ :=
    (cmp_m64_imm8_effect_step 0x100156 (.sib 4 none 0 (.none))
      (by decide) rfl rfl 0).advances hReady hc hp
      (text_address_ne_return hOutside 0x15b (by decide +kernel))
  have hmem : u.external = s.external := he.agrees.external (by
    simp [cmpM64Imm8Effect, Effect.components, Component.Covers])
  have hcu := hCode.of_external_eq hmem
  have hCond : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      decide ((Operand.mem (stackPtr s) : Operand 64).read s = 0) := by
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = _
    rw [he.flags.2.2.2.1]
    rw [haddr]
    change (((Operand.mem (stackPtr s) : Operand 64).read s - 0) == 0) = _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [BitVec.sub_eq_iff_eq_add]
    rfl
  have hNext : (jccEffect 0x10015b 2 4 ((16#8).signExtend 64) u).rip =
      (if (Operand.mem (stackPtr s) : Operand 64).read s = 0 then
        0x10016d else 0x10015d) := by
    change (if condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) then _ else _) = _
    rw [hCond]
    simp only [decide_eq_true_eq]
    rfl
  have hnb : (jccEffect 0x10015b 2 4 ((16#8).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x16d (by decide +kernel)
    · exact text_address_ne_return hOutside 0x15d (by decide +kernel)
  have hbc : CodeIn (codeRange 0x10015b [0x74, 16]) u :=
    program_text_slice hcu 0x15b 2 (by decide +kernel)
  obtain ⟨t, hb, ht, he'⟩ := (jcc_rel8_effect_step 0x10015b 4 16).advances hu hbc
    ⟨he.rip, fun _ => by decide +kernel⟩ hnb
  refine ⟨t, ha.trans hb, ht, he'.codeIn (branchEffect_avoids _ _ _ _) hcu,
    he'.rip.trans hNext, ?_⟩
  exact (he.agrees.trans he'.agrees).mono (by simp [cmpM64Imm8Effect,
    Effect.components, jccEffect, branchEffect])

theorem lowerEncodeAbiSuccess [Bindings] {initial s : RamState} (value : BitVec 64)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x10015d) (hsp : stackPtr s = stackPtr initial - 24)
    (hm : MemReadable s (stackPtr initial - 16) 8)
    (hvalue : (Operand.mem (stackPtr initial - 16) : Operand 64).read s = value)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rbx) 8)
    (hcode : ∀ i < 8, ¬ InProgram (s.regValue .rbx + BitVec.ofNat 64 i))
    (hsepB : RangeApart (s.regValue .rbx) 8 (stackPtr initial - 8) 8)
    (hsepR : RangeApart (s.regValue .rbx) 8 (stackPtr initial) 8)
    (hmb : MemReadable s (stackPtr initial - 8) 8)
    (hbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx)
    (hmret : MemReadable s (stackPtr initial) 8)
    (hv : (Operand.mem (stackPtr initial) : Operand 64).read s = (returnBoundary initial).rip)
    (hl : (returnBoundary initial).rip.toNat < 2^32)
    (ho : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Returns (returnBoundary initial) 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 3, .reg 4, .flags, .rip, .mem (s.regValue .rbx) 8] s t ∧
      t.regValue .rax = 0 ∧ t.regValue .rbx = initial.regValue .rbx ∧
      (Operand.mem (s.regValue .rbx) : Operand 64).read t = value := by
  have haddr : stackPtr s + 8 = stackPtr initial - 16 := by
    rw [hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hc1 : CodeIn (codeRange 0x10015d [0x48, 0x8b, 0x44, 0x24, 8]) s := by
    have hbytes : Extracted.textBytes.toListFrom 0x15d 5 = [0x48, 0x8b, 0x44, 0x24, 8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x15d = 0x10015d by decide +kernel]
      using program_text_slice hc 0x15d 5 (by decide +kernel)
  obtain ⟨u, run1, ready1, e1⟩ :=
    (mov_r64_m64_effect_step 0x10015d 0x48 (by constructor <;> decide +kernel) 0
      (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid]) rfl rfl).advances hr hc1
      ⟨hip, by change MemReadable s (stackPtr s + 8) 8; rw [haddr]; exact hm⟩
      (text_address_ne_return ho 0x162 (by decide +kernel))
  have a1 : AgreesExcept [.reg 0, .rip] s u := e1.agrees
  have mem1 : u.external = s.external := a1.external (by simp [Component.Covers])
  have bx1 : u.regValue .rbx = s.regValue .rbx := a1.read (n := 64) (r := 3) (by simp)
  have val1 : u.regValue .rax = value := by
    have hv1 := e1.writes
    change u.regValue .rax = (Operand.mem (stackPtr s + 8) : Operand 64).read s at hv1
    rw [haddr, hvalue] at hv1
    exact hv1
  have hc2 : CodeIn (codeRange 0x100162 [0x48, 0x89, 0x03]) u := by
    have hbytes : Extracted.textBytes.toListFrom 0x162 3 = [0x48, 0x89, 0x03] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x162 = 0x100162 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem1) 0x162 3 (by decide +kernel)
  have pre2 : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre 0x100162 3 (fun x => x.regValue .rbx) 8 u := by
    refine ⟨e1.rip, ?_, ?_⟩
    · rw [bx1]; exact hw.of_external_eq mem1
    · intro i hi j hj he
      apply hcode i hi
      rw [bx1] at he
      rw [he]
      have hsize : 0x162 + 3 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x162 + j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc,
        show Extracted.textAddress + BitVec.ofNat 64 0x162 = 0x100162 by decide +kernel] using hx
  have addr2 : storeAddrAt 0x100162 (.base 3 .none) 3 u = u.regValue .rbx := by
    change u.regValue .rbx + 0 = u.regValue .rbx
    exact BitVec.add_zero _
  have pre2a : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre 0x100162 3
      (storeAddrAt 0x100162 (.base 3 .none) 3) 8 u := by
    refine ⟨pre2.rip, ?_, ?_⟩
    · rw [addr2]; exact pre2.write
    · rw [addr2]; exact pre2.code
  obtain ⟨v, run2, ready2, e2⟩ :=
    (Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x100162 0x48
      (by constructor <;> decide +kernel) 0 (.base 3 .none)
      (by decide +kernel) rfl rfl).advances ready1 hc2 pre2a
      (text_address_ne_return ho 0x165 (by decide +kernel))
  have a2 : AgreesExcept [.mem (s.regValue .rbx) 8, .rip] u v := by
    have ha : AgreesExcept [.mem (storeAddrAt 0x100162 (.base 3 .none) 3 u) 8, .rip] u v := by
      simpa only [movM64R64Effect_components,
        show 3 + (AddrMode.base 3 .none).tail.length = 3 from rfl] using e2.agrees
    rw [addr2, bx1] at ha
    exact ha
  have hcV : CodeIn Extracted.programImage v := CodeIn.of_agreesExcept a2 (by
    intro x hx c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := hcov
      exact hcode i hi (he ▸ ⟨x.2, hx⟩)
    · exact hcov) (hc.of_external_eq mem1)
  have hc3 : CodeIn (codeRange 0x100165 [0x31, 0xc0]) v := by
    have hbytes : Extracted.textBytes.toListFrom 0x165 2 = [0x31, 0xc0] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x165 = 0x100165 by decide +kernel]
      using program_text_slice hcV 0x165 2 (by decide +kernel)
  obtain ⟨w, run3, ready3, e3⟩ :=
    (xor_r32_r32_effect_step 0x100165 0xc0 rfl).advances ready2 hc3 e2.rip
      (text_address_ne_return ho 0x167 (by decide +kernel))
  have a3 : AgreesExcept [.reg 0, .flags, .rip] v w := e3.agrees
  have mem3 : w.external = v.external := a3.external (by simp [Component.Covers])
  have aall := (a1.trans a2).trans a3
  have rsp3 : stackPtr w = stackPtr initial - 24 :=
    (aall.read (n := 64) (r := 4) (by simp)).trans hsp
  have slots (addr : BitVec 64) (ha : RangeApart (s.regValue .rbx) 8 addr 8) :
      (Operand.mem addr : Operand 64).read w = (Operand.mem addr : Operand 64).read s := by
    apply memLoad_congr
    intro i hi
    have he := aall.byte (x := addr + BitVec.ofNat 64 i) (by
      intro c hc hcov
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl)
      all_goals try exact hcov
      obtain ⟨j, hj, he⟩ := hcov
      exact ha j hj i hi he.symm)
    change (w.external[addr + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[addr + BitVec.ofNat 64 i]?).getD 0
    rw [he]
  have hc4 : CodeIn (codeRange 0x100167 [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3]) w := by
    have hbytes : Extracted.textBytes.toListFrom 0x167 6 = [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x167 = 0x100167 by decide +kernel]
      using program_text_slice (hcV.of_external_eq mem3) 0x167 6 (by decide +kernel)
  obtain ⟨t, run4, ready4, a4, bx4⟩ := restore_return 0x100167 ready3 hc4 e3.rip rsp3
    ⟨hmb.low, fun i hi => aall.grow _ (hmb.mem i hi)⟩
    ((slots _ hsepB).trans hbx)
    ⟨hmret.low, fun i hi => aall.grow _ (hmret.mem i hi)⟩
    ((slots _ hsepR).trans hv) hl
  refine ⟨t, ((run1.trans run2).trans run3).returns run4, ready4,
    (aall.trans a4).mono (by simp), ?_, bx4, ?_⟩
  · have hz : w.regValue .rax = 0 := by
      have he := e3.writes
      change w.regValue .rax =
        ((v.regValue .rax).setWidth 32 ^^^ (v.regValue .rax).setWidth 32).setWidth 64 at he
      rw [BitVec.xor_self] at he
      exact he
    exact (a4.read (n := 64) (r := 0) (by simp)).trans hz
  · have mt := a4.external (by simp [Component.Covers])
    change memLoad t.external _ 64 = _
    rw [mt, mem3]
    have he := e2.writes
    change memLoad v.external (u.regValue .rbx + 0#64) 64 = u.regValue .rax at he
    rw [BitVec.add_zero, bx1, val1] at he
    exact he


theorem lowerEncodeAbiFailure [Bindings] {initial s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x10016d) (hsp : stackPtr s = stackPtr initial - 24)
    (hm : MemReadable s (stackPtr initial - 16) 1)
    (hb : (Operand.mem (stackPtr initial - 16) : Operand 8).read s = 1)
    (hmb : MemReadable s (stackPtr initial - 8) 8)
    (hbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx)
    (hmret : MemReadable s (stackPtr initial) 8)
    (hv : (Operand.mem (stackPtr initial) : Operand 64).read s = (returnBoundary initial).rip)
    (hl : (returnBoundary initial).rip.toNat < 2^32)
    (ho : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Returns (returnBoundary initial) 6 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 1, .reg 3, .reg 4, .flags, .rip] s t ∧
      t.regValue .rax = 1 ∧ t.regValue .rbx = initial.regValue .rbx := by
  have haddr : stackPtr s + 8 = stackPtr initial - 16 := by
    rw [hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have hc1 : CodeIn (codeRange 0x10016d [0x0f, 0xb6, 0x4c, 0x24, 8]) s := by
    have hbytes : Extracted.textBytes.toListFrom 0x16d 5 = [0x0f, 0xb6, 0x4c, 0x24, 8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x16d = 0x10016d by decide +kernel]
      using program_text_slice hc 0x16d 5 (by decide +kernel)
  obtain ⟨u, run1, ready1, e1⟩ := (movzx_r32_m8_effect_step 0x10016d 1 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid]) rfl rfl).advances hr hc1
    ⟨hip, by change MemReadable s (stackPtr s + 8) 1; rw [haddr]; exact hm⟩ (text_address_ne_return ho 0x172 (by decide +kernel))
  have a1 : AgreesExcept [.reg 1, .rip] s u := e1.agrees
  have mem1 : u.external = s.external :=
    (a1.external (by simp [Component.Covers]))
  have hc2 : CodeIn (codeRange 0x100172 [0xb8, 2, 0, 0, 0]) u := by
    have hbytes : Extracted.textBytes.toListFrom 0x172 5 = [0xb8, 2, 0, 0, 0] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x172 = 0x100172 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem1) 0x172 5 (by decide +kernel)
  obtain ⟨v, run2, ready2, e2⟩ := (mov_r32_imm32_effect_step 0x100172 0xb8 (by decide +kernel) 2).advances ready1 hc2
    e1.rip (text_address_ne_return ho 0x177 (by decide +kernel))
  have a2 : AgreesExcept [.reg 0, .rip] u v := e2.agrees
  have mem2 : v.external = s.external :=
    (a2.external (by simp [Component.Covers])).trans mem1
  have hc3 : CodeIn (codeRange 0x100177 [0x29, 0xc8]) v := by
    have hbytes : Extracted.textBytes.toListFrom 0x177 2 = [0x29, 0xc8] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x177 = 0x100177 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem2) 0x177 2 (by decide +kernel)
  obtain ⟨w, run3, ready3, e3⟩ := (sub_r32_r32_effect_step 0x100177 0xc8 rfl).advances ready2 hc3
    e2.rip (text_address_ne_return ho 0x179 (by decide +kernel))
  have a3 : AgreesExcept [.reg 0, .flags, .rip] v w := e3.agrees
  have mem3 : w.external = s.external :=
    (a3.external (by simp [Component.Covers])).trans mem2
  have rsp3 : stackPtr w = stackPtr initial - 24 :=
    ((a1.trans a2).trans a3).read (n := 64) (r := 4) (by simp) |>.trans hsp
  have hc4 : CodeIn (codeRange 0x100179 [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3]) w := by
    have hbytes : Extracted.textBytes.toListFrom 0x179 6 = [0x48, 0x83, 0xc4, 0x10, 0x5b, 0xc3] := by decide +kernel
    simpa only [hbytes, show Extracted.textAddress + BitVec.ofNat 64 0x179 = 0x100179 by decide +kernel]
      using program_text_slice (hc.of_external_eq mem3) 0x179 6 (by decide +kernel)
  obtain ⟨t, run4, ready4, a4, bx4⟩ := restore_return 0x100179 ready3 hc4 e3.rip rsp3
    ⟨hmb.low, fun i hi => mem3 ▸ hmb.mem i hi⟩
    (by change memLoad w.external _ 64 = _; rw [mem3]; exact hbx)
    ⟨hmret.low, fun i hi => mem3 ▸ hmret.mem i hi⟩
    (by change memLoad w.external _ 64 = _; rw [mem3]; exact hv) hl
  refine ⟨t, ((run1.trans run2).trans run3).returns run4, ready4,
    (((a1.trans a2).trans a3).trans a4).mono (by simp), ?_, bx4⟩
  have hcx : u.regValue .rcx = 1 := by
    have hw := e1.writes
    change u.regValue .rcx = ((Operand.mem (stackPtr s + 8) : Operand 8).read s).setWidth 64 at hw
    rw [haddr, hb] at hw
    exact hw
  have hvax : v.regValue .rax = 2 := e2.writes
  have hvcx : v.regValue .rcx = 1 :=
    (a2.read (n := 64) (r := 1) (by simp)).trans hcx
  have hwax : w.regValue .rax = 1 := by
    have hw := e3.writes
    change w.regValue .rax = ((v.regValue .rax).setWidth 32 - (v.regValue .rcx).setWidth 32).setWidth 64 at hw
    rw [hvax, hvcx] at hw
    exact hw
  exact (a4.read (n := 64) (r := 0) (by simp)).trans hwax


end Base16ct.Proofs.LowerEncode
