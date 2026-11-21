import P256.Proofs.Common.Encoding.Parser.TagOps.Instructions
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

open P256.Proofs.Common.Encoding.Parser.TagOps (cmp_r8_imm8_form)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeOpcode80_r15b [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xff, t)) :
    (Decode_Legacy_0_Opcode_80 ip ctx).run s =
      (X86.Instructions.CMP_GPR8_IMMb_80r7 (BitVec.add ip 2#64) ctx 7).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_80 ctx true a b c d e f 0xff = .ok 16 := by
    rfl
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf hsel

def cmpR15bState (imm : UInt8) (s : RamState) : RamState :=
  afterStep s 4 fun t => writeFlagsOutputs t
    (cmpSpec ((Operand.reg 15 : Operand 8).read t) imm.toBitVec) 0 (BitVec.add s.RIP 4#64)

theorem cmp_r15b_step [Bindings] (s : RamState) (imm : UInt8) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x41, 0x80, 0xff, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (cmpR15bState imm s)) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1
    (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have fimm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  have hd := decodeLegacy0_run_of_opcode80 _ _ _ (rexContext s.DS 0x41) rfl fop (hmode 3)
  rw [decodeOpcode80_r15b _ _ _ _ (hmode 4) hf fmod,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _, cmp_r8_imm8_form _ _ _ _ _ _ (hmode 4) rfl rfl fimm,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hd
  have result := step_rex_legacy0 s _ h 0x41 0x80 [0xff, imm] (by simp [RexPrefix])
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)
  rw [show gprNumber (rexContext s.DS 0x41).rex_b4
    (rexContext s.DS 0x41).rex_b3 7 = 15#5 from rfl] at result
  simp only [BitVec.signExtend_eq, Operand.read_afterFetches, Operand.read_beforeFetch] at result
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact result

def cmpR15bEffect (p : BitVec 64) (imm : UInt8) (s : RamState) : Effect :=
  { rip := p + 4
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 15 : Operand 8).read s) imm.toBitVec)) }

theorem cmp_r15b_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x41, 0x80, 0xff, imm])
      (cmpR15bEffect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r15b_step s imm h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 0 _, ?_⟩
  refine ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩
  exact StatusFlagsOutcome.allows_ofStatusFlags _

@[x86_local] theorem cmpR15bEffect_local (p : BitVec 64) (imm : UInt8) :
    Effect.Local (cmpR15bEffect p imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpR15bEffect, h.read_reg]
  · intro s
    simp [cmpR15bEffect]

@[simp] theorem cmpR15bEffect_components (p : BitVec 64) (imm : UInt8) (s : RamState) :
    (cmpR15bEffect p imm s).components = [.flags, .rip] := rfl

attribute [x86_compose] cmpR15bEffect

end P256.Proofs.Projective.Multiply.Machine.Lookup.Instructions
