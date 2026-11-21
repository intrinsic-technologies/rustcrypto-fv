import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Entry
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.SysVEntry

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

abbrev entryCallSlots : List (BitVec 64 × BitVec 64) :=
  [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0), (0x201230, 0x101230)]

theorem fnCode_sub_programImage : ∀ x ∈ LIR.fnCode, x ∈ Extracted.programImage := by
  intro x hx
  change x ∈ ImageSections.toCodeMap [LIR.textSection] at hx
  change x ∈ ImageSections.toCodeMap [LIR.textSection, LIR.rodataSection]
  simp only [ImageSections.toCodeMap, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at hx ⊢
  exact Or.inl hx

theorem root_callSlots_loaded {m : FrameInfo} {initial : RamState}
    (hslots : m.callSlots = entryCallSlots) (hLoaded : ProgramLoaded initial) :
    ∀ c ∈ m.callSlots, Readable initial.external c.1 8 ∧
      memLoad initial.external c.1 64 = c.2 := by
  have hsection : m.CallSlotsIn LIR.rodataSection := by
    simp only [FrameInfo.CallSlotsIn, hslots]
    decide +kernel
  exact FrameInfo.callSlots_of_section
    (sections := Extracted.programSections) (by exact List.mem_cons_of_mem _ List.mem_cons_self)
    hsection (fun x hx => hLoaded x.1 x.2 hx)

theorem root_callSlots_span {m : FrameInfo} (hslots : m.callSlots = entryCallSlots) :
    ∀ a : BitVec 64, FrameInfo.slotsLow m.callSlots ≤ a.toNat →
      a.toNat < FrameInfo.slotsHigh m.callSlots → InProgram a := by
  have hsection : m.CallSlotSpanIn LIR.rodataSection := by
    simp only [FrameInfo.CallSlotSpanIn, hslots]
    decide +kernel
  exact FrameInfo.callSlotSpan_of_section
    (sections := Extracted.programSections) (by exact List.mem_cons_of_mem _ List.mem_cons_self)
    hsection

theorem root_lifted_entry {bindings : Bindings} {initial : RamState} {P : Lifted}
    {label : P.Label} {code : CodeMap}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hLoaded : ProgramLoaded initial) (hcode : ∀ x ∈ code, x ∈ Extracted.programImage)
    (hentry : initial.RIP = P.address label) :
    @Rel bindings code P ⟨P.locationOf label initial, []⟩ initial := by
  let _ : Bindings := bindings
  have hready := entryReady hMachine hBindings hLoaded
  exact Rel.locationOf ⟨hready.ready, hready.sse, CodeIn.mono hcode hready.code⟩ hentry

theorem root_simulation {bindings : Bindings} {initial : RamState} {boundary : ReturnBoundary}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hout : ¬ InProgram boundary.rip) :
    @Simulation (@machineAnyReturn bindings boundary)
      (LIR.lifted.program.sem (dialect Extracted.programImage))
      (@Rel bindings Extracted.programImage LIR.lifted)
      (@RetRel bindings Extracted.programImage LIR.lifted) := by
  let _ : Bindings := bindings
  apply LIR.simulation hBindings.stringStride Extracted.programImage fnCode_sub_programImage
  intro x hx heq
  exact hout ⟨x.2, heq ▸ hx⟩

end AesGcm.Proofs.Machine.Runtime
