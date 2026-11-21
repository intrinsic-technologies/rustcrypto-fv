import P256.Proofs.Common.Instructions.ByteOps
import X86Proofs.Instructions.And.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteOps.ByteOps

open X86 X86.Machine X86.UserProcess X86Proofs

def andAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let r := (Operand.reg 0 : Operand 8).read s &&& imm
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 r ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (andFlags r) }

def cmpAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  { rip := p + 2
    writes := []
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 0 : Operand 8).read s) imm)) }

theorem andAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8) (s : RamState) :
    (andAlImm8Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem andAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (andAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [andAlImm8Effect_components, Component.Covers]) code

theorem andAlImm8State_rax (s : RamState) (imm : BitVec 8) :
    (Operand.reg 0 : Operand 64).read (andAlImm8State s imm) =
      mergeGPR 8 ((Operand.reg 0 : Operand 8).read s &&& imm)
        ((Operand.reg 0 : Operand 64).read s) := by
  rw [andAlImm8State, Operand.read_afterStep]
  simp [writeOutputs, setFlags, Operand.read, Operand.write, andSpec, afterFetches, beforeFetch,
    resetStepFields]

theorem mergeGPR_low8 (v : BitVec 8) (old : BitVec 64) :
    (mergeGPR 8 v old).setWidth 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show ¬ (8 : Nat) = 32 by decide, ite_false, BitVec.getLsbD_setWidth,
    getLsbD_setSlice _ _ _ _ _ (by omega : k < 64)]
  simp [hk]

theorem andAlImm8State_low8 (s : RamState) (imm : BitVec 8) :
    (Operand.reg 0 : Operand 8).read (andAlImm8State s imm) =
      (Operand.reg 0 : Operand 8).read s &&& imm := by
  change ((Operand.reg 0 : Operand 64).read (andAlImm8State s imm)).setWidth 8 = _
  rw [andAlImm8State_rax, mergeGPR_low8]

theorem andAlImm8State_agrees (s : RamState) (imm : BitVec 8) :
    AgreesExcept [.reg 0, .flags, .rip] s (andAlImm8State s imm) :=
  AgreesExcept.afterStep_writeOutputs s 2 0 _ 1 _

theorem cmpAlImm8State_agrees (s : RamState) (imm : BitVec 8) :
    AgreesExcept [.flags, .rip] s (cmpAlImm8State s imm) :=
  AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 0 _

theorem andAlImm8State_rip [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    (andAlImm8State s imm).RIP = s.RIP + 2 :=
  afterStep_writeOutputs_rip h 2 _ _ 1 _

theorem cmpAlImm8State_rip [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    (cmpAlImm8State s imm).RIP = s.RIP + 2 :=
  afterStep_writeFlagsOutputs_rip h 2 _ 0 _

theorem cmpAlImm8State_flags (s : RamState) (imm : BitVec 8) :
    StatusFlags.ofRFLAGS (cmpAlImm8State s imm).RFLAGS =
      cmpSpec ((Operand.reg 0 : Operand 8).read s) imm := by
  change StatusFlags.ofRFLAGS ((cmpSpec _ imm).store s.RFLAGS) = _
  rw [StatusFlags.ofRFLAGS_store]
  rw [Operand.read_afterFetches, Operand.read_beforeFetch]

theorem cmpAlImm8State_ZF (s : RamState) (imm : BitVec 8) :
    (StatusFlags.ofRFLAGS (cmpAlImm8State s imm).RFLAGS).ZF =
      decide ((Operand.reg 0 : Operand 8).read s = imm) := by
  rw [cmpAlImm8State_flags]
  simp only [cmpSpec, subSpec]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  change (_ = BitVec.add 0#8 imm) ↔ _
  have hz : BitVec.add 0#8 imm = imm := BitVec.zero_add imm
  rw [hz]

theorem andAlImm8State_effect [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    (andAlImm8Effect s.RIP imm s).Holds s (andAlImm8State s imm) := by
  refine ⟨andAlImm8State_rip h imm, andAlImm8State_rax s imm,
    StatusFlagsOutcome.allows_store ?_ _, andAlImm8State_agrees s imm⟩
  exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem cmpAlImm8State_effect [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    (cmpAlImm8Effect s.RIP imm s).Holds s (cmpAlImm8State s imm) := by
  refine ⟨cmpAlImm8State_rip h imm, trivial, ?_, cmpAlImm8State_agrees s imm⟩
  change (StatusFlagsOutcome.ofStatusFlags _).Allows _
  rw [cmpAlImm8State_flags]
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem and_al_imm8_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x24, imm])
      (andAlImm8Effect p imm.toBitVec) := by
  rintro s h hcode rfl
  exact ⟨_, and_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_al_imm8_ready h imm.toBitVec,
    andAlImm8State_effect h imm.toBitVec⟩

theorem cmp_al_imm8_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x3c, imm])
      (cmpAlImm8Effect p imm.toBitVec) := by
  rintro s h hcode rfl
  exact ⟨_, cmp_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_al_imm8_ready h imm.toBitVec,
    cmpAlImm8State_effect h imm.toBitVec⟩

end P256.Proofs.Common.Instructions.ByteOps.ByteOps
