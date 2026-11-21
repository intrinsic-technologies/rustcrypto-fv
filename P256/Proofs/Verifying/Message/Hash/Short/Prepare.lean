import P256.Proofs.Verifying.Message.Hash.Entry
import P256.Proofs.Verifying.Message.Hash.Short.Setup
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Ready [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  memory : t.external = s.external
  rip : t.RIP = 0x10d621
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  source : t.regValue .rsi = memLoad initial.external (initial.regValue .rdx) 64
  destination : t.regValue .rdi = frameBase initial + 472
  count : t.regValue .rdx = BitVec.ofNat 64 message.size
  position : t.regValue .rbx = 0
  length : t.regValue .r15 = BitVec.ofNat 64 message.size

theorem prepare [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (entered : Entered initial s t boundary message) (short : message.size < 64) :
    ∃ u, Ready initial s u boundary message := by
  obtain ⟨a, stepA, readyA, branchA⟩ := jcc_rel8_effect_step 0x10d65d 2 0xb1 t
    (readyToStep entered.machine entered.bindingsSupported)
    (programText_slice (programLoaded_codeIn entered.loaded) 0xd65d _
      (by decide) (by decide +kernel)) ⟨entered.rip, by intro; decide⟩
  have carry : (StatusFlags.ofRFLAGS t.RFLAGS).CF = true := by
    rw [entered.carry]
    change decide ((BitVec.ofNat 64 message.size).toNat < (64#64).toNat) = true
    simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
    omega
  have ripA : a.RIP = 0x10d610 := by
    rw [branchA.rip]
    change (if (StatusFlags.ofRFLAGS t.RFLAGS).CF then 0x10d610 else 0x10d65f) = _
    rw [carry]
    rfl
  have runA : Advances boundary 1 t a := Advances.of_step stepA (.inl (by
    rw [ripA]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd610 (by decide))))
  have agA : AgreesExcept [.rip] t a := branchA.agrees
  have stateA := entered.toFrameState.after_registers readyA agA (by simp [Component.Covers]) (by simp)
  obtain ⟨fuelB, b, runB, readyB, _, effectB⟩ := Setup.run boundary pre.outerBoundary a readyA
    (Setup.code stateA.loaded) ripA
  have agB : AgreesExcept [.reg 7,.reg 6,.reg 2,.flags,.rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB agB (by simp [Component.Covers]) (by simp)
  have positionA : a.regValue .rbx = 0 := (agA.read (n := 64) (r := 3) (by simp)).trans entered.position
  have sourceA : a.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64 :=
    (agA.read (n := 64) (r := 14) (by simp)).trans entered.source
  have lengthA : a.regValue .r15 = BitVec.ofNat 64 message.size :=
    (agA.read (n := 64) (r := 15) (by simp)).trans entered.length
  have writes := effectB.writes
  change b.regValue .rdi = stackPtr a + a.regValue .rbx + 472 ∧
    b.regValue .rsi = a.regValue .r14 ∧ b.regValue .rdx = a.regValue .r15 at writes
  rw [positionA, sourceA, lengthA] at writes
  refine ⟨b, stateB, ?_, ((agA.trans agB).external (by simp [Component.Covers])).trans entered.memory,
    effectB.rip, ((agA.trans agB).read (n := 64) (r := 13) (by simp)).trans entered.current,
    ((agA.trans agB).read (n := 64) (r := 12) (by simp)).trans entered.endPointer,
    writes.2.1, ?_, writes.2.2,
    (agB.read (n := 64) (r := 3) (by simp)).trans positionA,
    (agB.read (n := 64) (r := 15) (by simp)).trans lengthA⟩
  · obtain ⟨fuel, run⟩ := entered.execution
    exact ⟨fuel + 1 + fuelB, (run.trans runA).trans runB⟩
  · have h : stackPtr a = frameBase initial := stateA.rsp
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, h] using writes.1

end P256.Proofs.Verifying.Message.Hash.Short
