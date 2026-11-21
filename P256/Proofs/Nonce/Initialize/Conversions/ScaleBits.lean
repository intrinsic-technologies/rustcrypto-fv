import P256.Proofs.Common.Instructions.Lea32.NoBase

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions.Lea32

theorem lea_r9d_r8_scale8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x46, 0x8D, 0x0C, 0xC5, 0, 0, 0, 0])
    (hlow : s.RIP.toNat + 8 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 8 fun t =>
      writeResult t (.reg 9 : Operand 32)
        (((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)).setWidth 32) (BitVec.add s.RIP 8#64))) := by
  have hd := decodeLegacy0_run_of_rex_8D s h 0x46 0x0C (by decide) [0xC5, 0, 0, 0, 0]
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      [0x46, 0x8D, 0x0C, 0xC5, 0, 0, 0, 0] := hcode
  have hsib := memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
    (by decide) (by decide)
  have hdisp := memFetch_run_of_bytesAt_imm (beforeFetch s) 5 h.fetchReady hc hlow 32
    (by decide) 0 4 (immBytes_getElem?_append [0x46, 0x8D, 0x0C, 0xC5] (0#32))
    (by decide) (by decide)
  have hmode (n : Nat) : In64BitMode (afterFetches (beforeFetch s) n) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdisp' : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 3#64) 1#64) 32).run
      (afterFetches (beforeFetch s) 5) = (.ok 0#32, afterFetches (beforeFetch s) 9) := by
    rw [show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _]
    exact hdisp
  have hea := effectiveAddress_noBase_run _ _ _ (rexContext s.DS 0x46) (BitVec.add s.RIP 3#64) 8 3 0
    (by decide) rfl rfl rfl rfl rfl rfl hsib (hmode 5) hdisp'
  have hea' : (Effective_Address 64 (rexContext s.DS 0x46) 0 4 1 (BitVec.add s.RIP 3#64)).run
      (afterFetches (beforeFetch s) 4) =
      (.ok ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat), nullDataSegment s.DS,
        BitVec.add s.RIP 8#64, false, false), afterFetches (beforeFetch s) 9) := by
    simp only [AddrMode.reg64, Operand.read_afterFetches, Operand.read_beforeFetch] at hea
    change (Effective_Address 64 (rexContext s.DS 0x46) 0 4 1 (BitVec.add s.RIP 3#64)).run
        (afterFetches (beforeFetch s) 4) =
        (.ok (BitVec.add ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)) 0#64, nullDataSegment s.DS,
          BitVec.add (BitVec.add s.RIP 3#64) 5#64, false, false), afterFetches (beforeFetch s) 9) at hea
    have hz : BitVec.add ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)) 0#64 =
        (Operand.reg 8 : Operand 64).read s <<< (3 : Nat) := BitVec.add_zero _
    rw [hz,
      show BitVec.add (BitVec.add s.RIP 3#64) 5#64 =
      BitVec.add s.RIP 8#64 from BitVec.add_assoc _ _ _] at hea
    exact hea
  change (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS 0x46)).run
      (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 3#64)
        (rexContext s.DS 0x46) 0 1 4).run (afterFetches (beforeFetch s) 4)) at hd
  have hrip : Handle_RIP_Relative_Address 64 false
      ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)) (BitVec.add s.RIP 8#64) =
      .ok ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)) :=
    handleRIPRelativeAddress64_run false _ _
  rw [lea_r32_m_form _ _ _ _ 0 1 4 rfl rfl rfl _ _ _ _ _ hea' hrip (hmode 9)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x46 0x8D [0x0C, 0xC5, 0, 0, 0, 0]
    (by simp [RexPrefix]) (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow hd ((hmode 9).of_cs_lma_eq rfl rfl)

theorem lea_r9d_r8_scale8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x46, 0x8D, 0x0C, 0xC5, 0, 0, 0, 0])
      (leaR32NoBaseEffect p 9 8 3 0) := by
  rintro s h hcode rfl
  refine ⟨_, lea_r9d_r8_scale8_step s h hcode.bytesAt (hcode.low (by decide) (by decide)),
    ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  change _ = ((BitVec.add ((Operand.reg 8 : Operand 64).read s <<< (3 : Nat)) 0#64).setWidth 32).setWidth 64
  exact congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) (BitVec.add_zero _).symm

end P256.Proofs.Nonce.Initialize.Conversions
