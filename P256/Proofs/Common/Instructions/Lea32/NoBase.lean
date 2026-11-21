import P256.Proofs.Common.Instructions.Lea32

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Lea32

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem readSIB_noBase_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (index : BitVec 4) (scale : BitVec 2) (disp : BitVec 32)
    (hindex : index ≠ 4) (hb3 : ctx.rex_b3 = 0) (hb4 : ctx.rex_b4 = 0)
    (hx3 : ctx.rex_x3 = regHigh index) (hx4 : ctx.rex_x4 = 0)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s =
      (.ok (AddrMode.sibByte 5 (some index) scale).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : (Mem_Fetch (BitVec.add ip 1#64) 32).run t = (.ok disp, u)) :
    (Read_SIB ctx 0 1 ip).run s =
      (.ok (nullDataSegment u.DS, disp.signExtend 64, AddrMode.reg64 index t,
        ((2 ^ scale.toNat : Nat) : Int), BitVec.add ip 5#64, false), u) := by
  unfold Read_SIB
  refine (specM_bind_run _ _ hsib).trans ?_
  simp (config := { decide := true }) only [X86.Runtime.sliceInclusive,
    X86.Runtime.CheckedSlice.read, slice_eq_pure, pure_bind, Int.reduceToNat, Int.reduceSub,
    Int.reduceAdd, sibByte_toBitVec, append_hi, append_mid, append_lo, exp2_scale, hb3, hb4,
    hx3, hx4, concatBits_hi2, idxLow, concatBits_reg5, HOr.hOr, OrOp.or, strictOr,
    getEffectiveSegment_run ctx _ hseg hm64, setWidth5_ne4 index hindex]
  spec_run [Read_GPR => readGPR64_run _ _ hmode, MonadState.get => get_run _,
    Mem_Fetch => hdisp]

theorem effectiveAddress_noBase_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (index : BitVec 4) (scale : BitVec 2) (disp : BitVec 32)
    (hindex : index ≠ 4) (hb3 : ctx.rex_b3 = 0) (hb4 : ctx.rex_b4 = 0)
    (hx3 : ctx.rex_x3 = regHigh index) (hx4 : ctx.rex_x4 = 0)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s =
      (.ok (AddrMode.sibByte 5 (some index) scale).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : (Mem_Fetch (BitVec.add ip 1#64) 32).run t = (.ok disp, u)) :
    (Effective_Address 64 ctx 0 4 1 ip).run s =
      (.ok ((AddrMode.reg64 index t <<< scale.toNat) + disp.signExtend 64,
        nullDataSegment u.DS, BitVec.add ip 5#64, false, false), u) := by
  have hr := readSIB_noBase_run s t u ctx ip index scale disp hindex hb3 hb4 hx3 hx4 hseg
    hm64 hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  rw [getEffectiveSegment_run ctx _ hseg hm64]
  have hm (x : BitVec 64) : x * BitVec.ofInt 64 (2 ^ scale.toNat) = x <<< scale.toNat := by
    simpa using mul_pow_shift x scale.toNat
  simp [nullDataSegment_idem, hm, BitVec.add_comm]

theorem lea_ecx_r12_scale4_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x42, 0x8D, 0x0C, 0xA5, 0, 0, 0, 0])
    (hlow : s.RIP.toNat + 8 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 8 fun t =>
      writeResult t (.reg 1 : Operand 32)
        (((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)).setWidth 32) (BitVec.add s.RIP 8#64))) := by
  have hd := decodeLegacy0_run_of_rex_8D s h 0x42 0x0C (by decide) [0xA5, 0, 0, 0, 0]
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      [0x42, 0x8D, 0x0C, 0xA5, 0, 0, 0, 0] := hcode
  have hsib := memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
    (by decide) (by decide)
  have hdisp := memFetch_run_of_bytesAt_imm (beforeFetch s) 5 h.fetchReady hc hlow 32
    (by decide) 0 4 (immBytes_getElem?_append [0x42, 0x8D, 0x0C, 0xA5] (0#32))
    (by decide) (by decide)
  have hmode (n : Nat) : In64BitMode (afterFetches (beforeFetch s) n) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdisp' : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 3#64) 1#64) 32).run
      (afterFetches (beforeFetch s) 5) = (.ok 0#32, afterFetches (beforeFetch s) 9) := by
    rw [show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _]
    exact hdisp
  have hea := effectiveAddress_noBase_run _ _ _ (rexContext s.DS 0x42) (BitVec.add s.RIP 3#64) 12 2 0
    (by decide) rfl rfl rfl rfl rfl rfl hsib (hmode 5) hdisp'
  have hea' : (Effective_Address 64 (rexContext s.DS 0x42) 0 4 1 (BitVec.add s.RIP 3#64)).run
      (afterFetches (beforeFetch s) 4) =
      (.ok ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat), nullDataSegment s.DS,
        BitVec.add s.RIP 8#64, false, false), afterFetches (beforeFetch s) 9) := by
    simp only [AddrMode.reg64, Operand.read_afterFetches, Operand.read_beforeFetch] at hea
    change (Effective_Address 64 (rexContext s.DS 0x42) 0 4 1 (BitVec.add s.RIP 3#64)).run
        (afterFetches (beforeFetch s) 4) =
        (.ok (BitVec.add ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)) 0#64, nullDataSegment s.DS,
          BitVec.add (BitVec.add s.RIP 3#64) 5#64, false, false), afterFetches (beforeFetch s) 9) at hea
    have hz : BitVec.add ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)) 0#64 =
        (Operand.reg 12 : Operand 64).read s <<< (2 : Nat) := BitVec.add_zero _
    rw [hz,
      show BitVec.add (BitVec.add s.RIP 3#64) 5#64 =
      BitVec.add s.RIP 8#64 from BitVec.add_assoc _ _ _] at hea
    exact hea
  change (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS 0x42)).run
      (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 3#64)
        (rexContext s.DS 0x42) 0 1 4).run (afterFetches (beforeFetch s) 4)) at hd
  have hrip : Handle_RIP_Relative_Address 64 false
      ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)) (BitVec.add s.RIP 8#64) =
      .ok ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)) :=
    handleRIPRelativeAddress64_run false _ _
  rw [lea_r32_m_form _ _ _ _ 0 1 4 rfl rfl rfl _ _ _ _ _ hea' hrip (hmode 9)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x42 0x8D [0x0C, 0xA5, 0, 0, 0, 0]
    (by simp [RexPrefix]) (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow hd ((hmode 9).of_cs_lma_eq rfl rfl)

def leaR32NoBaseEffect (p : BitVec 64) (dst index : BitVec 5) (scale : Nat)
    (disp : BitVec 32) (s : RamState) : Effect :=
  { rip := p + 8
    writes := [⟨(Operand.reg dst : Operand 64),
      ((((Operand.reg index : Operand 64).read s <<< scale) +
        disp.signExtend 64).setWidth 32).setWidth 64⟩] }

theorem lea_ecx_r12_scale4_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x42, 0x8D, 0x0C, 0xA5, 0, 0, 0, 0])
      (leaR32NoBaseEffect p 1 12 2 0) := by
  rintro s h hcode rfl
  refine ⟨_, lea_ecx_r12_scale4_step s h hcode.bytesAt (hcode.low (by decide) (by decide)),
    ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  change _ = ((BitVec.add ((Operand.reg 12 : Operand 64).read s <<< (2 : Nat)) 0#64).setWidth 32).setWidth 64
  exact congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) (BitVec.add_zero _).symm

end P256.Proofs.Common.Instructions.Lea32
