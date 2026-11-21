import Sha3.Proofs.Update.Partial.Control
import Sha3.Proofs.Scalar.Address.Lea
import Sha3.Proofs.X86.Instructions.MemAlu.Decode
import Sha3.Proofs.X86.Instructions.Cmp.Imm8.Triple
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Add.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Sha3.Proofs.Update.Partial.FillControl

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers Sha3.Spec.Program

private theorem lea_r32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x8D :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (2 + am.tail.length) fun t ↦
      writeResult t (.reg (gprNumber 0 0 reg) : Operand 32)
        ((am.addrAt s (2 + am.tail.length)).setWidth 32)
        (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))))) := by
  have hlow' : s.RIP.toNat + (0x8D :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_8D s h (am.modrm reg) am.tail
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x8D :: am.modrm reg :: am.tail) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j _ ↦ by simp only [Nat.add_comm, List.getElem?_cons_succ]) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show 3 + am.tail.length = 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) =
      am.addrAt s (2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)))
  rw [haddr] at hrip
  rw [lea_r32_m_form _ t _ _ _ _ _ rfl rfl rfl _ _ _ _ _ hea hrip hmode] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x8D _
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def leaR32Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (2 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64),
      ((am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))).setWidth 32).setWidth 64⟩] }

private theorem lea_r32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p (0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (gprNumber 0 0 reg) am) := by
  rintro s h hcode rfl
  refine ⟨_, lea_r32_step s h reg am hv hx hb hcode.bytesAt
    (by
      have hl := hcode.low (by simp) (by have := am.tail_length_le; simp; omega)
      simp only [List.length_cons] at hl
      omega),
    ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  exact Operand.read_writeResult_self32 _ _ _ _

private theorem decode_cmp_sil [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xfe, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.CMP_GPR8_IMMb_80r7 (BitVec.add ip 2#64) context 6).run t := by
  unfold Decode_Legacy_0_Opcode_80
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive (0xfe#8) 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive (0xfe#8) 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_0_Opcode_80 context mode a b c d e f 0xfe) _ 16 hmode hf
    (fun a b c d e f ↦ by
      simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
        bind, pure, Except.bind, Except.pure, HAnd.hAnd, AndOp.and, strictAnd])).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

private theorem cmp_sil_form [Bindings] (s t : RamState) (ip : BitVec 64) (seg : Segment)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok 3, t)) :
    (X86.Instructions.CMP_GPR8_IMMb_80r7 ip (rexContext seg 0x40) 6).run s =
      (.ok (), writeFlagsOutputs t (cmpSpec ((Operand.reg 6 : Operand 8).read s) 3) 0
        (BitVec.add ip 1#64)) := by
  unfold X86.Instructions.CMP_GPR8_IMMb_80r7
  simp only [rexContext, writeFlagsOutputs, oracleSkip_zero]
  spec_run [Read_GPR8 => readGPR8_run_of_rex _ _ hmode, Mem_Fetch => hfetch,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

private theorem cmp_sil_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x40, 0x80, 0xfe, 3]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeFlagsOutputs t (cmpSpec ((Operand.reg 6 : Operand 8).read t) 3) 0
        (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x40, 0x80, 0xfe, 3] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x80, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by decide) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok 0xfe, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by decide) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have hdecode := decodeLegacy0_run_of_opcode80 _ _ (BitVec.add s.RIP 1#64)
    (rexContext s.DS 0x40) rfl f2 (hm 3)
  rw [decode_cmp_sil _ _ _ _ (hm 4) hf f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x40, 0x80, 0xfe, 3] := hcode
  have himm := memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
    (by decide) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  change (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
    (.ok 3, afterFetches (beforeFetch s) 5) at himm
  rw [cmp_sil_form _ _ (BitVec.add s.RIP 3#64) s.DS (hmode 4) himm,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x40 0x80 [0xfe, 3]
    (by unfold RexPrefix; decide) (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

def cmpSilEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := []
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 6 : Operand 8).read s) 3)) }

private theorem cmp_sil_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x40, 0x80, 0xfe, 3]) (cmpSilEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_sil_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial,
      StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩⟩


def leaDisp (v : Variant) : BitVec 8 := BitVec.ofNat 8 (259 - v.rate)

theorem mask_arithmetic (n : Fin 145) :
    ((((BitVec.ofNat 64 n.val).setWidth 32).setWidth 64).setWidth 32 &&& 3#32).setWidth 64 =
      BitVec.ofNat 64 (n.val % 4) ∧
    (((((BitVec.ofNat 64 n.val).setWidth 32).setWidth 64).setWidth 32) &&&
      (0xfc#8).signExtend 32).setWidth 64 = BitVec.ofNat 64 (4 * (n.val / 4)) := by
  revert n
  decide +kernel

theorem cursor_arithmetic (v : Variant) (position : Fin v.rate) (hp : 0 < position.val) :
    (!decide (((((BitVec.ofNat 64 position.val + (leaDisp v).signExtend 64).setWidth 32).setWidth
      64).setWidth 8).toNat < 3)) = decide (4 ≤ v.rate - position.val) := by
  cases v <;> revert position <;> decide +kernel

theorem chunk_setup [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState) (remaining : Fin 145)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0x6a#64)
    (hremaining : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 remaining.val) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + 0x80#64 ∧
      (Operand.reg 10 : Operand 64).read t = BitVec.ofNat 64 (4 * (remaining.val / 4)) ∧
      (Operand.reg 6 : Operand 64).read t = 0 ∧
      (Operand.reg 8 : Operand 64).read t =
        (Operand.reg 0 : Operand 64).read s + (Operand.reg 15 : Operand 64).read s + 3 ∧
      AgreesExcept [.reg 10, .reg 6, .reg 8, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalar_model_advance (v := v)
    (effect := movR32R32Effect (v.updateAddress + 0x6a#64) 3 10 2)
    (mov_r32_r32_rex_effect_step (v.updateAddress + 0x6a#64) 0x41 0xd2 (by unfold RexNoWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32R32Effect, h.read_reg])
    (by intro c hc; exact hc) (by simp [movR32R32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x6a#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x6d (by decide))
    hready hcode hb hip (Obs.refl s)
  obtain ⟨s2, a2, r2, c2, e2, o2, f2⟩ := scalar_model_advance (v := v)
    (effect := andR32Imm8Effect (v.updateAddress + 0x6d#64) 4 10 0xfc)
    (and_r32_imm8_rex_effect_step (v.updateAddress + 0x6d#64) 0x41 0xe2 0xfc (by unfold RexNoWPrefix; decide) (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [andR32Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR32Imm8Effect, h.read_reg])
    (by intro c hc; exact hc) (by simp [andR32Imm8Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x6d#64 + 0x4#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x71 (by decide))
    r1 c1 hb (by simpa only [movR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e1.rip) o1
  obtain ⟨s3, a3, r3, c3, e3, o3, f3⟩ := scalar_model_advance (v := v)
    (effect := leaR64Effect (v.updateAddress + 0x71#64) 8 (.sib 0 (some 15) 0 .none))
    (lea_r64_effect_step (v.updateAddress + 0x71#64) 0x4e (by unfold RexWPrefix; decide) 0 (.sib 0
      (some 15) 0 .none) (by decide) (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [leaR64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR64Effect, AddrMode.addr_obs h])
    (by intro c hc; exact hc) (by simp [leaR64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x71#64 + 0x4#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x75 (by decide))
    r2 c2 hb (by simpa only [andR32Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e2.rip) o2
  obtain ⟨s4, a4, r4, c4, e4, o4, f4⟩ := scalar_model_advance (v := v)
    (effect := addR64Imm8Effect (v.updateAddress + 0x75#64) 8 3)
    (add_r64_imm8_effect_step (v.updateAddress + 0x75#64) 0x49 0xc0 3 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64Imm8Effect, h.read_reg])
    (by intro c hc; exact hc) (by simp [addR64Imm8Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x75#64 + 0x4#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x79 (by decide))
    r3 c3 hb (by simpa only [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, List.length_cons,
      List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
      using e3.rip) o3
  obtain ⟨s5, a5, r5, c5, e5, o5, f5⟩ := scalar_model_advance (v := v)
    (effect := xorR32R32Effect (v.updateAddress + 0x79#64) 2 6 6)
    (xor_r32_r32_effect_step (v.updateAddress + 0x79#64) 0xf6 (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by intro c hc; exact hc) (by simp [xorR32R32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x79#64 + 0x2#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x7b (by decide))
    r4 c4 hb (by simpa only [addR64Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e4.rip) o4
  obtain ⟨s6, a6, r6, c6, e6, o6, f6⟩ := scalar_model_advance (v := v)
    (effect := fun _ ↦ nopEffect (v.updateAddress + 0x7b#64) 5)
    (nop_m_effect_step (v.updateAddress + 0x7b#64) [] (by decide) (by decide) (.sib
      0 (some 0) 0 (.d8 0)) (by decide) (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [nopEffect, Write.Full, Operand.Full])
    (by intro a b h; rfl)
    (by intro c hc; exact hc) (by simp [nopEffect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x7b#64 + 0x5#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        offset_inProgram v 0x80 (by decide))
    r5 c5 hb (by simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e5.rip) o5
  refine ⟨s6, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6), r6, c6, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [nopEffect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e6.rip
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect]
    have hs : (Operand.reg 2 : Operand 32).read s =
        ((Operand.reg 2 : Operand 64).read s).setWidth 32 := rfl
    simp only [BitVec.ofNat_eq_ofNat] at hs hremaining
    rw [hs, hremaining]
    exact (mask_arithmetic remaining).2
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, BitVec.xor_self]
  · first | rw [← o6.read_reg] | rw [← o6.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · apply (((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans
      e5.agrees).trans e6.agrees).mono
    simp [movR32R32Effect, andR32Imm8Effect, leaR64Effect, addR64Imm8Effect,
      xorR32R32Effect, nopEffect, Effect.components]

theorem byte_setup [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0xb8#64) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + 0xd0#64 ∧
      (Operand.reg 0 : Operand 64).read t = (Operand.reg 0 : Operand 64).read s +
        (Operand.reg 15 : Operand 64).read s + (Operand.reg 6 : Operand 64).read s ∧
      (Operand.reg 6 : Operand 64).read t =
        (Operand.reg 6 : Operand 64).read s + (Operand.reg 3 : Operand 64).read s ∧
      (Operand.reg 7 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 0, .reg 6, .reg 7, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalar_model_advance (v := v)
    (effect := addR64R64Effect (v.updateAddress + 0xb8#64) 0 15) (add_r64_r64_effect_step
      (v.updateAddress + 0xb8#64) 0x4c 0xf8 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [addR64R64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xb8#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xbb (by decide))
    hready hcode hb hip (Obs.refl s)
  have ip1 : s1.RIP = v.updateAddress + 0xbb#64 := by
    have h : s1.RIP = v.updateAddress + 0xb8#64 + 0x3#64 := e1.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s2, a2, r2, c2, e2, o2, f2⟩ := scalar_model_advance (v := v)
    (effect := addR64R64Effect (v.updateAddress + 0xbb#64) 0 6) (add_r64_r64_effect_step
      (v.updateAddress + 0xbb#64) 0x48 0xf0 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [addR64R64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xbb#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xbe (by decide))
    r1 c1 hb ip1 o1
  have ip2 : s2.RIP = v.updateAddress + 0xbe#64 := by
    have h : s2.RIP = v.updateAddress + 0xbb#64 + 0x3#64 := e2.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s3, a3, r3, c3, e3, o3, f3⟩ := scalar_model_advance (v := v)
    (effect := addR64R64Effect (v.updateAddress + 0xbe#64) 6 3) (add_r64_r64_effect_step
      (v.updateAddress + 0xbe#64) 0x48 0xde (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [addR64R64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xbe#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xc1 (by decide))
    r2 c2 hb ip2 o2
  have ip3 : s3.RIP = v.updateAddress + 0xc1#64 := by
    have h : s3.RIP = v.updateAddress + 0xbe#64 + 0x3#64 := e3.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s4, a4, r4, c4, e4, o4, f4⟩ := scalar_model_advance (v := v)
    (effect := xorR32R32Effect (v.updateAddress + 0xc1#64) 2 7 7) (xor_r32_r32_effect_step
      (v.updateAddress + 0xc1#64) 0xff (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [xorR32R32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xc1#64 + 0x2#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xc3 (by decide))
    r3 c3 hb ip3 o3
  have ip4 : s4.RIP = v.updateAddress + 0xc3#64 := by
    have h : s4.RIP = v.updateAddress + 0xc1#64 + 0x2#64 := e4.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s5, a5, r5, c5, e5, o5, f5⟩ := scalar_model_advance (v := v)
    (effect := fun _ ↦ nopEffect (v.updateAddress + 0xc3#64) 13) (nop_m_effect_step (v.updateAddress
      + 0xc3#64) [0x66, 0x66, 0x66, 0x66, 0x2e] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
      (by decide) (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [nopEffect, Write.Full, Operand.Full])
    (by intro a b h; rfl) (by intro c hc; exact hc)
    (by simp [nopEffect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xc3#64 + 0xd#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xd0 (by decide))
    r4 c4 hb ip4 o4
  have ip5 : s5.RIP = v.updateAddress + 0xd0#64 := by
    have h : s5.RIP = v.updateAddress + 0xc3#64 + 0xd#64 := e5.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  refine ⟨s5, (((a1.trans a2).trans a3).trans a4).trans a5, r5, c5, ip5, ?_, ?_, ?_, ?_⟩
  · first | rw [← o5.read_reg] | rw [← o5.read_mem]
    x86_norm [addR64R64Effect, xorR32R32Effect, nopEffect]
  · first | rw [← o5.read_reg] | rw [← o5.read_mem]
    x86_norm [addR64R64Effect, xorR32R32Effect, nopEffect]
  · first | rw [← o5.read_reg] | rw [← o5.read_mem]
    x86_norm [addR64R64Effect, xorR32R32Effect, nopEffect, BitVec.xor_self]
  · apply ((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).mono
    simp [addR64R64Effect, xorR32R32Effect, nopEffect, Effect.components]

theorem finish [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0xe1#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + 0xe7#64 ∧
      (Operand.reg 3 : Operand 64).read t =
        (Operand.reg 3 : Operand 64).read s + (Operand.reg 2 : Operand 64).read s ∧
      (Operand.reg 7 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s ∧
      AgreesExcept [.reg 3, .reg 7, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalar_model_advance (v := v)
    (effect := addR64R64Effect (v.updateAddress + 0xe1#64) 3 2) (add_r64_r64_effect_step
      (v.updateAddress + 0xe1#64) 0x48 0xd3 (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [addR64R64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xe1#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xe4 (by decide))
    hready hcode hb hip (Obs.refl s)
  have ip1 : s1.RIP = v.updateAddress + 0xe4#64 := by
    have h : s1.RIP = v.updateAddress + 0xe1#64 + 0x3#64 := e1.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s2, a2, r2, c2, e2, o2, f2⟩ := scalar_model_advance (v := v)
    (effect := movR64R64Effect (v.updateAddress + 0xe4#64) 7 15) (mov_r64_r64_effect_step
      (v.updateAddress + 0xe4#64) 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [movR64R64Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0xe4#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0xe7 (by decide))
    r1 c1 hb ip1 o1
  have ip2 : s2.RIP = v.updateAddress + 0xe7#64 := by
    have h : s2.RIP = v.updateAddress + 0xe4#64 + 0x3#64 := e2.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  refine ⟨s2, a1.trans a2, r2, c2, ip2, ?_, ?_, ?_⟩
  · first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [addR64R64Effect, movR64R64Effect]
  · first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [addR64R64Effect, movR64R64Effect]
  · apply (e1.agrees.trans e2.agrees).mono
    simp [addR64R64Effect, movR64R64Effect, Effect.components]

theorem small_setup [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0x66#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + 0xb8#64 ∧ (Operand.reg 6 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 6, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalar_model_advance (v := v)
    (effect := xorR32R32Effect (v.updateAddress + 0x66#64) 2 6 6) (xor_r32_r32_effect_step
      (v.updateAddress + 0x66#64) 0xf6 (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [xorR32R32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x66#64 + 0x2#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0x68 (by decide))
    hready hcode hb hip (Obs.refl s)
  have ip1 : s1.RIP = v.updateAddress + 0x68#64 := by
    have h : s1.RIP = v.updateAddress + 0x66#64 + 0x2#64 := e1.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have target : branchTarget (v.updateAddress + 0x68#64) 2 (BitVec.signExtend 64 0x4e#8) =
      v.updateAddress + 0xb8#64 := by
    simp only [branchTarget, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend]
  obtain ⟨t, a2, r2, c2, e2⟩ := scalar_advance (v := v)
    (jmp_rel8_effect_step (v.updateAddress + 0x68#64) 0x4e#8
      (by rw [target]; cases v <;> decide))
    (by cases v <;> decide +kernel) r1 c1 ip1
    (by simp [Component.Covers])
    (by simpa only [jmpEffect, target] using offset_inProgram v 0xb8 (by decide)) hb
  refine ⟨t, a1.trans a2, r2, c2, e2.rip.trans target, ?_, ?_⟩
  · rw [e2.agrees.read (by simp), ← o1.read_reg]
    x86_norm [xorR32R32Effect, BitVec.xor_self]
  · apply (e1.agrees.trans e2.agrees).mono
    simp [xorR32R32Effect, jmpEffect, Effect.components]

theorem dispatch [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState) (position : Fin v.rate)
    (hposition : 0 < position.val)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0x54#64)
    (hcursor : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 position.val)
    (hremaining : (Operand.reg 2 : Operand 64).read s =
      BitVec.ofNat 64 (v.rate - position.val)) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + 0x60#64 ∧
      condHolds 3#4 (StatusFlags.ofRFLAGS t.RFLAGS) = decide (4 ≤ v.rate - position.val) ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 ((v.rate - position.val) % 4) ∧
      AgreesExcept [.reg 1, .reg 6, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1, o1, f1⟩ := scalar_model_advance (v := v)
    (effect := movR32R32Effect (v.updateAddress + 0x54#64) 2 1 2) (mov_r32_r32_effect_step
      (v.updateAddress + 0x54#64) 0xd1 (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32R32Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [movR32R32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x54#64 + 0x2#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0x56 (by decide))
    hready hcode hb hip (Obs.refl s)
  have ip1 : s1.RIP = v.updateAddress + 0x56#64 := by
    have h : s1.RIP = v.updateAddress + 0x54#64 + 0x2#64 := e1.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s2, a2, r2, c2, e2, o2, f2⟩ := scalar_model_advance (v := v)
    (effect := andR32Imm8Effect (v.updateAddress + 0x56#64) 3 1 3) (and_r32_imm8_effect_step
      (v.updateAddress + 0x56#64) 0xe1 3 (by decide) (by decide))
    (by cases v <;> decide +kernel)
    (by intro t; simp [andR32Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR32Imm8Effect, h.read_reg]) (by intro c hc; exact hc)
    (by simp [andR32Imm8Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x56#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0x59 (by decide))
    r1 c1 hb ip1 o1
  have ip2 : s2.RIP = v.updateAddress + 0x59#64 := by
    have h : s2.RIP = v.updateAddress + 0x56#64 + 0x3#64 := e2.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s3, a3, r3, c3, e3, o3, f3⟩ := scalar_model_advance (v := v)
    (effect := leaR32Effect (v.updateAddress + 0x59#64) 6 (.base 0 (.d8 (leaDisp v))))
      (lea_r32_effect_step (v.updateAddress + 0x59#64) 6 (.base 0 (.d8 (leaDisp v))) (by cases v <;>
      decide) rfl rfl)
    (by cases v <;> decide +kernel)
    (by intro t; simp [leaR32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [leaR32Effect, AddrMode.addr_obs h]) (by intro c hc; exact hc)
    (by simp [leaR32Effect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x59#64 + 0x3#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0x5c (by decide))
    r2 c2 hb ip2 o2
  have ip3 : s3.RIP = v.updateAddress + 0x5c#64 := by
    have h : s3.RIP = v.updateAddress + 0x59#64 + 0x3#64 := e3.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  obtain ⟨s4, a4, r4, c4, e4, o4, f4⟩ := scalar_model_advance (v := v)
    (effect := cmpSilEffect (v.updateAddress + 0x5c#64)) (cmp_sil_effect_step (v.updateAddress +
      0x5c#64))
    (by cases v <;> decide +kernel)
    (by intro t; simp [cmpSilEffect, Write.Full, Operand.Full])
    (by intro a b h; rfl) (by intro c hc; exact hc)
    (by simp [cmpSilEffect, Effect.components, Component.Covers])
    (by
      change InProgram (v.updateAddress + 0x5c#64 + 0x4#64)
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using offset_inProgram v 0x60 (by decide))
    r3 c3 hb ip3 o3
  have ip4 : s4.RIP = v.updateAddress + 0x60#64 := by
    have h : s4.RIP = v.updateAddress + 0x5c#64 + 0x4#64 := e4.rip
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hsil : (Operand.reg 6 : Operand 8).read s3 =
      (((BitVec.ofNat 64 position.val + (leaDisp v).signExtend 64).setWidth 32).setWidth
        64).setWidth 8 := by
    first | rw [← o3.read_reg] | rw [← o3.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect, leaR32Effect]
    have hc := hcursor
    simp only [BitVec.ofNat_eq_ofNat] at hc
    rw [hc]
  have hcf : condHolds 3#4 (StatusFlags.ofRFLAGS s4.RFLAGS) =
      decide (4 ≤ v.rate - position.val) := by
    have h := e4.flags.1
    change (StatusFlags.ofRFLAGS s4.RFLAGS).CF =
      decide (((Operand.reg 6 : Operand 8).read s3).toNat < 3) at h
    change (!(StatusFlags.ofRFLAGS s4.RFLAGS).CF) = _
    rw [h, hsil]
    exact cursor_arithmetic v position hposition
  refine ⟨s4, ((a1.trans a2).trans a3).trans a4, r4, c4, ip4, hcf, ?_, ?_⟩
  · rw [e4.agrees.read (by simp [cmpSilEffect, Effect.components]), ← o3.read_reg]
    x86_norm [movR32R32Effect, andR32Imm8Effect, leaR32Effect]
    have hs : (Operand.reg 2 : Operand 32).read s =
        ((Operand.reg 2 : Operand 64).read s).setWidth 32 := rfl
    have hr := hremaining
    simp only [BitVec.ofNat_eq_ofNat] at hs hr
    rw [hs, hr]
    have hn : v.rate - position.val < 145 := by
      have hr : v.rate ≤ 144 := by cases v <;> decide
      omega
    exact (mask_arithmetic ⟨v.rate - position.val, hn⟩).1
  · apply (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).mono
    simp [movR32R32Effect, andR32Imm8Effect, leaR32Effect, cmpSilEffect, Effect.components]

theorem dispatch_branch [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0x64#64) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if condHolds 3#4 (StatusFlags.ofRFLAGS s.RFLAGS) then
        v.updateAddress + 0x6a#64 else v.updateAddress + 0x66#64) ∧
      AgreesExcept [.rip] s t := by
  have target : branchTarget (v.updateAddress + 0x64#64) 2 (BitVec.signExtend 64 4#8) =
      v.updateAddress + 0x6a#64 := by
    simp only [branchTarget, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend]
  obtain ⟨t, ha, hr, hc, he⟩ := scalar_advance (v := v)
    (jcc_rel8_effect_step (v.updateAddress + 0x64#64) 3#4 4#8)
    (by cases v <;> decide +kernel) hready hcode
    ⟨hip, fun _ ↦ by rw [target]; cases v <;> decide⟩
    (by simp [jccEffect, Component.Covers])
    (by
      simp only [jccEffect, branchEffect, target, BitVec.add_assoc, BitVec.reduceAdd]
      split <;> exact offset_inProgram v _ (by decide)) hb
  refine ⟨t, ha, hr, hc, ?_, he.agrees⟩
  simpa only [jccEffect, branchEffect, target, BitVec.add_assoc, BitVec.reduceAdd] using he.rip

theorem post_chunk [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + 0xb3#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (Operand.reg 1 : Operand 64).read s = 0 then v.updateAddress + 0xe1#64
        else v.updateAddress + 0xb8#64) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1⟩ := scalar_advance (v := v)
    (effect := testR64R64Effect (v.updateAddress + 0xb3#64) 1#5 1#5)
    (test_r64_r64_effect_step (v.updateAddress + 0xb3#64) 0x48 0xc9
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) hready hcode hip
    (by simp [Component.Covers])
    (by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using
      offset_inProgram v 0xb6 (by decide)) hb
  have hz : condHolds 4#4 (StatusFlags.ofRFLAGS s1.RFLAGS) =
      ((Operand.reg 1 : Operand 64).read s == 0) := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 1 : Operand 64).read s &&& (Operand.reg 1 : Operand 64).read s) == 0) at h
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = _
    simpa only [BitVec.and_self] using h
  have target : branchTarget (v.updateAddress + 0xb6#64) 2 (BitVec.signExtend 64 0x29#8) =
      v.updateAddress + 0xe1#64 := by
    simp only [branchTarget, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend]
  obtain ⟨t, a2, r2, c2, e2⟩ := scalar_advance (v := v)
    (jcc_rel8_effect_step (v.updateAddress + 0xb6#64) 4#4 0x29#8)
    (by cases v <;> decide +kernel) r1 c1
    ⟨by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using e1.rip,
      fun _ ↦ by rw [target]; cases v <;> decide⟩
    (by simp [jccEffect, Component.Covers])
    (by
      simp only [jccEffect, branchEffect, target, BitVec.add_assoc, BitVec.reduceAdd]
      split <;> exact offset_inProgram v _ (by decide)) hb
  refine ⟨t, a1.trans a2, r2, c2, ?_, ?_⟩
  · simpa only [jccEffect, branchEffect, target, hz, beq_iff_eq,
      BitVec.add_assoc, BitVec.reduceAdd] using e2.rip
  · apply (e1.agrees.trans e2.agrees).mono
    simp [testR64R64Effect, jccEffect, branchEffect, Effect.components]

end Sha3.Proofs.Update.Partial.FillControl
