import P256.Spec.Program.Functions
import P256.Proofs.Program.CallPre
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure SavedEntry [Bindings] (initial s : RamState) : Prop where
  execution : Advances (returnBoundary initial) 7 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x1067d1
  rsp : stackPtr s = stackPtr initial - 504
  memory : s.external = saveMemory initial
  agrees : AgreesExcept (saveFrame initial ++ [.reg 4, .flags, .rip]) initial s

theorem save_correct [bindings : Bindings] {s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (call : ValidCallWithSlices ecdhDiffieHellman s [secret, peer] slices) :
    ∃ t, SavedEntry s t := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    save_registers (codeOffset := 0x67c0) call.stackAvailable.1 (call_stack_avoids call)
      (outer_boundary call hm hb) (readyToStep hm hb) call.programLoaded (by decide)
      call.atEntryPoint (by constructor <;> decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x67ca 456 readyU loadedU (outer_boundary call hm hb) ripU
      (by decide) (by decide +kernel)
  refine ⟨t, ⟨runU.trans runT, readyT, loadedT, ripT, ?_, memoryT.trans memoryU,
    agreesU.trans agreesT⟩⟩
  rw [rspT, rspU, BitVec.sub_sub]
  rfl

theorem SavedEntry.frame [Bindings] {s t : RamState}
    (stack : Stack.Valid s ecdhDiffieHellman.minStackBytes) (saved : SavedEntry s t) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman s) := by
  apply saved.agrees.memoryWriteFrame
  intro c hc a hv
  rcases List.mem_append.mp hc with hc | hc
  · simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals refine ⟨callStack ecdhDiffieHellman s, by simp [wrapperRegions], ?_⟩
    · exact stack_component_within stack (offset := 8) (by decide) (by decide) hv
    · exact stack_component_within stack (offset := 16) (by decide) (by decide) hv
    · exact stack_component_within stack (offset := 24) (by decide) (by decide) hv
    · exact stack_component_within stack (offset := 32) (by decide) (by decide) hv
    · exact stack_component_within stack (offset := 40) (by decide) (by decide) hv
    · exact stack_component_within stack (offset := 48) (by decide) (by decide) hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact hv.elim

end P256.Proofs.EcdhWrapper
