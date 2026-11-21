import P256.Proofs.Verifying.Wrapper.Tag
import P256.Proofs.Verifying.Wrapper.SuccessControl
import P256.Proofs.Verifying.Wrapper.SuccessStore
import P256.Proofs.Verifying.Wrapper.SuccessMemory
import P256.Proofs.Verifying.Wrapper.Restore
import P256.Proofs.Program.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem accept [bindings : Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (accepted : verifyingKeyVerify.accepts #[key, signature, message] = true)
    (state : ReturnState initial s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : s.RIP = 0x1031e9) (output : s.regValue .r12 = initial.regValue .rcx)
    (capacity : s.regValue .r13 = initial.regValue .r8)
    (tag : loadBytes s.external (stackPtr initial - 208) 8 = .ok (0 : BitVec 64)) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      SuccessfulStatus t ∧
      MemoryWriteFrame s t #v[outputRegion verifyingKeyVerify initial [key, signature, message]] ∧
      readOutput verifyingKeyVerify initial t = .ok .empty := by
  obtain ⟨a, ha, stateA, ripA, memoryA, agreesA⟩ :=
    tag_branch (valid := true) state call.stackAvailable.1 outside rip tag
  have capacityA : 8 ≤ (a.regValue .r13).toNat := by
    have capA : a.regValue .r13 = initial.regValue .r8 :=
      (agreesA.read (n := 64) (r := 13) (by simp)).trans capacity
    rw [capA]
    have h := call.outputSufficesIfAccepted accepted
    exact Nat.le_trans (by omega) h
  obtain ⟨b, hb, readyB, ripB, agreesB⟩ :=
    capacity_guard (readyToStep stateA.machine stateA.bindingsSupported) stateA.loaded
      outside ripA capacityA
  have stateB := stateA.after_registers readyB agreesB
    (by simp [Component.Covers]) (by simp) (by simp)
  have outputB : b.regValue .r12 = initial.regValue .rcx :=
    ((agreesA.trans agreesB).read (n := 64) (r := 12) (by simp)).trans output
  have pre : SuccessStorePre b := by
    refine ⟨ripB, ?_, ?_⟩
    · rw [outputB]
      exact output_writable call accepted stateB
    · rw [outputB]
      exact output_code call accepted (offset := 0x3216) (len := 10) (by decide)
  obtain ⟨n, c, hc, readyC, _, effectC⟩ := success_store (returnBoundary initial) outside b readyB
    (programText_slice (programLoaded_codeIn stateB.loaded) 0x3216 successStoreBytes
      (by decide) (by decide +kernel)) pre
  have agreesC : AgreesExcept [.mem (initial.regValue .rcx) 8, .reg 0, .flags, .rip] b c := by
    have h := effectC.agrees
    simpa only [successStoreEffect, Effect.components, Write.component, Operand.component,
      List.map, List.cons_append, List.nil_append, Nat.reduceDiv, outputB] using h
  have stateC := stateB.after_output call accepted readyC agreesC
  have word : memLoad c.external (initial.regValue .rcx) 64 = 0 := by
    have h := effectC.writes.1
    change memLoad c.external (b.regValue .r12) 64 = 0 at h
    simpa only [outputB] using h
  have cBytes := Bytes.of_memLoad (n := 64) (output_writable call accepted stateC).mem
  rw [word] at cBytes
  obtain ⟨t, ht, machine, binding, saved, direction, memory, status⟩ :=
    restore stateC call.stackAvailable.1 outside low effectC.rip
  refine ⟨_, t, ((ha.trans hb).trans hc).returns ht, machine, binding, saved, direction, ?_, ?_, ?_⟩
  · change (t.regValue .rax).setWidth 32 = 0
    have hc : c.regValue .rax = 0 := effectC.writes.2
    rw [status, hc]
    rfl
  · have frame := output_frame call accepted agreesC
    intro address away
    rw [memory, frame address away]
    exact ((agreesA.trans agreesB).external (by simp [Component.Covers])) ▸ rfl
  · apply readOutput_of_bytes (by decide)
    · change Bytes t.external (initial.regValue .rcx) 8 (storedByte (0 : BitVec 64))
      rw [memory]
      exact cBytes
    · intro i hi
      change i < 0 at hi
      omega

end P256.Proofs.Verifying.Wrapper
