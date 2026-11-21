import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Step.LegacyStep

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem readSIB_rax8_run [Bindings] (s t u : RamState) (seg : Segment) (ip : BitVec 64)
    (hsib : (Mem_Fetch ip 8).run s = (.ok 0xC5, t))
    (hmode : In64BitMode t)
    (hdisp : (Mem_Fetch (BitVec.add ip 1#64) 32).run t = (.ok 0, u)) :
    (Read_SIB (legacyContext seg) 0 1 ip).run s =
      (.ok (nullDataSegment u.DS, 0, (Operand.reg 0 : Operand 64).read t, 8,
        BitVec.add ip 5#64, false), u) := by
  change (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte 5 (some 0) 3).toBitVec, t) at hsib
  unfold Read_SIB
  refine (specM_bind_run _ _ hsib).trans ?_
  simp (config := { decide := true }) only [X86.Runtime.sliceInclusive,
    X86.Runtime.CheckedSlice.read, slice_eq_pure, pure_bind, Int.reduceToNat, Int.reduceSub,
    Int.reduceAdd, sibByte_toBitVec, append_hi, append_mid, append_lo, exp2_scale,
    legacyContext, HOr.hOr, OrOp.or, strictOr]
  spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp,
    MonadState.get => get_run _]

theorem effectiveAddress_rax8_run [Bindings] (s t u : RamState) (seg : Segment)
    (ip : BitVec 64) (hsib : (Mem_Fetch ip 8).run s = (.ok 0xC5, t))
    (hmode : In64BitMode t)
    (hdisp : (Mem_Fetch (BitVec.add ip 1#64) 32).run t = (.ok 0, u)) :
    (Effective_Address 64 (legacyContext seg) 0 4 1 ip).run s =
      (.ok (BitVec.mul ((Operand.reg 0 : Operand 64).read t) 8#64, nullDataSegment u.DS,
        BitVec.add ip 5#64, false, false), u) := by
  have hr := readSIB_rax8_run s t u seg ip hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  change (Except.ok (BitVec.add 0#64 (BitVec.mul ((Operand.reg 0 : Operand 64).read t) 8#64),
    nullDataSegment u.DS, BitVec.add ip 5#64, false, false), u) = _
  rw [show BitVec.add 0#64 (BitVec.mul ((Operand.reg 0 : Operand 64).read t) 8#64) =
    BitVec.mul ((Operand.reg 0 : Operand 64).read t) 8#64 from BitVec.zero_add _]

theorem decodeLegacy0_run_of_8D [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (rest : List UInt8) (hmod : modrmMod modrm ≠ 3)
    (hcode : BytesAt s s.RIP (0x8D :: modrm :: rest))
    (hlow : s.RIP.toNat + (0x8D :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x8D :: modrm :: rest) := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x8D, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode8D _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode8D_run_of_memory _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem lea_ecx_rax8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x8D, 0x0C, 0xC5, 0, 0, 0, 0])
    (hlow : s.RIP.toNat + 7 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 7 fun t ↦
      writeResult t (.reg 1 : Operand 32)
        (((Operand.reg 0 : Operand 64).read s * 8).setWidth 32)
        (BitVec.add s.RIP 7#64))) := by
  have hdecode := decodeLegacy0_run_of_8D s h 0x0C [0xC5, 0, 0, 0, 0]
    (by decide) hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      [0x8D, 0x0C, 0xC5, 0, 0, 0, 0] := hcode
  have hsib : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run
      (afterFetches (beforeFetch s) 3) =
      (.ok 0xC5, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by simp) (by decide)
  have hcimm : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0x8D :: 0x0C :: 0xC5 :: immBytes 32 0) := hc
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hcimm hlow
    32 (by decide) 0 3 (immBytes_getElem?_append [0x8D, 0x0C, 0xC5] 0) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdisp : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 32).run
      (afterFetches (beforeFetch s) 4) = (.ok 0, afterFetches (beforeFetch s) 8) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _]
    exact himm
  have hea := effectiveAddress_rax8_run _ _ _ s.DS (BitVec.add s.RIP 2#64)
    hsib (hmode 4) hdisp
  rw [show BitVec.add (BitVec.add s.RIP 2#64) 5#64 = BitVec.add s.RIP 7#64 from
    BitVec.add_assoc _ _ _] at hea
  change (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run
      (afterFetches (beforeFetch s) 1) =
    some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 2#64)
      (legacyContext s.DS) 0 1 4).run (afterFetches (beforeFetch s) 3)) at hdecode
  have hrip := handleRIPRelativeAddress64_run false
    (BitVec.mul ((Operand.reg 0 : Operand 64).read s) 8#64) (BitVec.add s.RIP 7#64)
  rw [lea_r32_m_form _ _ _ _ 0 1 4 rfl rfl rfl _ _ _ _ _ hea hrip (hmode 8)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x8D [0x0C, 0xC5, 0, 0, 0, 0]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    ((hmode 8).of_cs_lma_eq rfl rfl)

def leaEcxRax8Effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 7
    writes := [⟨(Operand.reg 1 : Operand 64),
      (((Operand.reg 0 : Operand 64).read s * 8).setWidth 32).setWidth 64⟩] }

theorem lea_ecx_rax8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x8D, 0x0C, 0xC5, 0, 0, 0, 0])
      (leaEcxRax8Effect p) := by
  rintro s h hcode rfl
  refine ⟨_, lea_ecx_rax8_step s h hcode.bytesAt
    (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  exact Operand.read_writeResult_self32 _ _ _ _

end X86Proofs
