import P256.Proofs.Verifying.Wrapper.Tag
import P256.Proofs.Verifying.Wrapper.RejectControl
import P256.Proofs.Verifying.Wrapper.Restore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reject [bindings : Bindings] {initial s : RamState}
    (state : ReturnState initial s) (stack : Stack.Valid initial 10280)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : s.RIP = 0x1031e9)
    (tag : loadBytes s.external (stackPtr initial - 208) 8 = .ok (1 : BitVec 64))
    (null : loadBytes s.external (stackPtr initial - 200) 8 = .ok (0 : BitVec 64)) :
    ∃ t, Returns (returnBoundary initial) 14 s t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      FailureStatus t invalidSignatureStatus ∧ t.external = s.external := by
  obtain ⟨a, ha, stateA, ripA, memoryA, _⟩ :=
    tag_branch (valid := false) state stack outside rip tag
  obtain ⟨b, hb, stateB, ripB, statusB, memoryB⟩ :=
    reject_branch stateA stack outside ripA (by simpa only [memoryA] using null)
  obtain ⟨t, ht, machine, bindingsSupported, saved, direction, memory, status⟩ :=
    restore stateB stack outside low ripB
  refine ⟨t, (ha.trans hb).returns ht, machine, bindingsSupported, saved, direction, ?_,
    memory.trans (memoryB.trans memoryA)⟩
  change (t.regValue .rax).setWidth 32 = 1
  rw [status, statusB]
  rfl

end P256.Proofs.Verifying.Wrapper
