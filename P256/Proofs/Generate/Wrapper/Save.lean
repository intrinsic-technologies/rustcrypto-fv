import P256.Proofs.Pkcs8.Save

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Pkcs8 (saveMemory saveComponents)

structure SavedEntry [Bindings] (initial s : RamState) : Prop where
  execution : Advances (returnBoundary initial) 4 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x106d3c
  rsp : stackPtr s = stackPtr initial - 264
  memory : s.external = saveMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s
  frame : MemoryWriteFrame initial s (wrapperRegions signingKeyGenerateFromRng initial)

theorem save_correct [bindings : Bindings] {s : RamState} {input : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (h : ValidCallWithSlices signingKeyGenerateFromRng s [input] slices) :
    ∃ t, SavedEntry s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, ag⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x6d30) [15,14,3]
      h.stackAvailable.1 (call_stack_avoids h) (outer_boundary h hm hb)
      (readyToStep hm hb) h.programLoaded (fun _ ha => ha) (by simp) h.atEntryPoint
      (by decide) (by decide) (by decide) (fun _ _ => rfl) (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, runt, readyt, loadedt, ript, rspt, memoryt, agt⟩ :=
    stack_allocate32 0x6d35 240 ready loaded (outer_boundary h hm hb) rip
      (by decide) (by decide +kernel)
  have agrees : AgreesExcept (saveComponents s) s t := by
    apply (ag.trans agt).mono
    intro c hc
    simp only [pushSequenceFrame, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      rfl | rfl | rfl
    all_goals simp [saveComponents]
  refine ⟨t, ⟨run.trans runt, readyt, loadedt, ript, ?_, ?_, agrees, ?_⟩⟩
  · rw [rspt, rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · exact memoryt.trans memory
  · apply agrees.memoryWriteFrame
    intro c hc a hv
    simp only [saveComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals refine ⟨callStack signingKeyGenerateFromRng s, by simp [wrapperRegions], ?_⟩
    · exact stack_component_within h.stackAvailable.1 (offset := 8) (by decide) (by decide) hv
    · exact stack_component_within h.stackAvailable.1 (offset := 16) (by decide) (by decide) hv
    · exact stack_component_within h.stackAvailable.1 (offset := 24) (by decide) (by decide) hv

end P256.Proofs.Generate.Wrapper
