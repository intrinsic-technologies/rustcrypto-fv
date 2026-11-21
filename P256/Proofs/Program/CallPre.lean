import P256.Proofs.Program.Interface
import P256.Proofs.Program.Stack
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {routine : Routine} {s : RamState}
  {inputs : List ByteArray} {slices : Array Input}

omit bindings in
theorem stack_contains_callStack {s : RamState} {address : Nat}
    (h : (Stack.region s routine.minStackBytes).Contains address) :
    (callStack routine s).Contains address := by
  change (s.regValue .rsp).toNat - routine.minStackBytes ≤ address ∧
    address < (s.regValue .rsp).toNat - routine.minStackBytes +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - routine.minStackBytes)) at h
  change (s.regValue .rsp).toNat - routine.minStackBytes ≤ address ∧
    address < (s.regValue .rsp).toNat - routine.minStackBytes +
      ((s.regValue .rsp).toNat + 16 - ((s.regValue .rsp).toNat - routine.minStackBytes))
  constructor <;> omega

theorem call_stack_avoids (h : ValidCallWithSlices routine s inputs slices) :
    (Stack.region s routine.minStackBytes).Avoids (fun a => InProgram a ∨ InPageTables a) := by
  intro a ha
  exact (h.separation.2 (callStack routine s) (by simp)).2 a
    (stack_contains_callStack ha)

theorem initial_boundary (h : ValidCallWithSlices routine s inputs slices)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (hb : MachineRamUnitStrideDecodable bindings s) :
    nearReturn64Boundary s = .ok (returnBoundary s) := by
  have hr := readyToStep hm hb
  apply nearReturn64Boundary_eq s hr.dataReady hr.cpu.ss
  have hs : Stack.Valid s routine.minStackBytes := h.stackAvailable.1
  simpa only [BitVec.sub_zero] using
    (stack_sub_readable hs (offset := 0) (len := 8) (Nat.zero_le _) (by decide))

theorem outer_boundary (h : ValidCallWithSlices routine s inputs slices)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (hb : MachineRamUnitStrideDecodable bindings s) :
    ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨b, he, _, hout⟩ := h.returnAddress
  have he' := initial_boundary h hm hb
  rw [he'] at he
  cases he
  exact hout

end P256.Proofs.Program
