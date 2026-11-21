import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem Prepared.of_control {l : Layout} {sp : BitVec 64} {prior : ByteArray} {input : Input}
    {s t : RamState} (data : Prepared l sp prior input {s with RIP := l.entry})
    (agrees : AgreesExcept [.flags, .rip] s t) :
    Prepared l sp prior input {t with RIP := l.entry} := by
  have read (r : BitVec 5) : (.reg r : Operand 64).read t = (.reg r : Operand 64).read s :=
    agrees.read (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨rfl, (read 4).trans data.rsp, ?_, (read _).trans data.source,
    (read _).trans data.length, (read _).trans data.position, ?_, data.bounded, data.messageBound,
    fun r member => (read _).trans (data.bufferRegister r member),
    fun call member r encoding => (read _).trans (data.copyRegister call member r encoding)⟩
  · exact data.hasher.of_bytes (fun _ _ => by simp only [memory])
  · exact ⟨data.bytes.1, fun i => by simpa only [memory] using data.bytes.2 i⟩

theorem select_empty [Bindings] {l : Layout} {initial before s : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve) (state : Preserved l initial before s regions)
    (data : Prepared l (l.sp initial) prior input {s with RIP := l.entry})
    (rip : s.RIP = l.pc .emptyTest) :
    ∃ t, Preserved l initial before t regions ∧
      Prepared l (l.sp initial) prior input {t with RIP := l.entry} ∧
      t.RIP = (if prior.size % 64 = 0 then l.pc .emptySetup else l.pc .fillSetup) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, stateU, test⟩ := run_stage ctx state .emptyTest rfl rip data.bufferRegister
    (by intro h; cases h)
  have agreesU : AgreesExcept [.flags, .rip] s u := test.agrees
  have dataU := data.of_control agreesU
  obtain ⟨t, stateT, branch⟩ := run_stage ctx stateU .emptyBranch rfl test.rip dataU.bufferRegister
    (by intro h; cases h)
  have agreesT : AgreesExcept [.flags, .rip] u t := branch.agrees.mono (by simp [Stage.effect,
    branchEffect, Effect.components])
  have flags := test.flags
  have value : Blocks.readReg s l.registers.tail = BitVec.ofNat 64 (prior.size % 64) := data.position
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = decide (prior.size % 64 = 0) := by
    have h := flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Blocks.readReg s l.registers.tail &&& Blocks.readReg s l.registers.tail) == 0) at h
    rw [h, BitVec.and_self, value]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, BitVec.reduceToNat,
        Nat.mod_eq_of_lt (by omega : prior.size % 64 < 2^64)] using h
    · intro eq
      rw [eq]
      rfl
  have agrees : AgreesExcept [.flags, .rip] s t :=
    (agreesU.trans agreesT).mono (by simp)
  refine ⟨t, stateT, data.of_control agrees, ?_, agrees⟩
  rw [branch.rip]
  change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then _ else _) = _
  rw [zero]
  simp only [decide_eq_true_eq]

end Sha2.Proofs.Common.SHA256.Absorb
