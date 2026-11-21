import P256.Proofs.Common.Instructions.ByteLogic.Unary

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions.ByteLogic
open scoped X86.Runtime.Syntax

theorem decode_not_r15b [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xd7, t)) :
    (Decode_Legacy_0_Opcode_F6 ip ctx).run s =
      (X86.Instructions.NOT_GPR8 (BitVec.add ip 2#64) ctx 7).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_F6 ctx true a b c d e f 0xd7 = .ok 12 := by rfl
  unfold Decode_Legacy_0_Opcode_F6
  decode_modrm_form s t ip hfetch hmode hf hsel

def notR15bState (s : RamState) : RamState :=
  afterStep s 3 fun t => writeResult t (.reg 15 : Operand 8)
    (notSpec ((Operand.reg 15 : Operand 8).read t)) (BitVec.add s.RIP 3#64)

theorem not_r15b_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x41, 0xf6, 0xd7]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (notR15bState s)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x41, 0xf6, 0xd7] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xf6, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok 0xd7, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeF6 _ _ _ (rexContext s.DS (0x41 : UInt8).toBitVec) rfl f2 (hm 3)
  rw [decode_not_r15b _ _ _ _ (hm 4) hf f3,
    not_r8_form _ _ _ _ (hm 4) rfl (.inl rfl)] at hd
  rw [show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
    BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h 0x41 0xf6 [0xd7] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd ((hm 4).of_cs_lma_eq rfl rfl)

def notR15bEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 15 : Operand 64),
      mergeGPR 8 (~~~((Operand.reg 15 : Operand 8).read s))
        ((Operand.reg 15 : Operand 64).read s)⟩] }

theorem not_r15b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0xf6, 0xd7]) (notR15bEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, not_r15b_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 15 _ _, ?_⟩
  refine ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
    AgreesExcept.afterStep_writeResult s 3 15 _ _⟩
  change (Operand.reg 15 : Operand 64).read (notR15bState s) = _
  rw [notR15bState, Operand.read_afterStep]
  simp [writeResult, Operand.read, Operand.write, notSpec, afterFetches,
    beforeFetch, resetStepFields]

end P256.Proofs.Sec1.Affine.Uncompressed.Output
