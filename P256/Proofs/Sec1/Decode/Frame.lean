import P256.Proofs.Sec1.Decode.Prologue
import P256.Proofs.Program.PushSequenceFrame
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedSlots : List (Syntax.Reg × Nat) := [(.r15, 8), (.r14, 16), (.r12, 24), (.rbx, 32)]

theorem savedMemory_slots (s : RamState) (slot : Syntax.Reg × Nat) (member : slot ∈ savedSlots) :
    memLoad (savedMemory s) (stackPtr s - BitVec.ofNat 64 slot.2) 64 = s.regValue slot.1 := by
  simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    simp only [savedMemory, savedRegisters, pushSequenceMemory]
    change memLoad
      (memStore (memStore (memStore (memStore s.external (stackPtr s - 8) (s.regValue .r15))
        (stackPtr s - 16) (s.regValue .r14)) (stackPtr s - 24) (s.regValue .r12))
        (stackPtr s - 32) (s.regValue .rbx)) _ 64 = _
    simp only [BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

structure Frame [bindings : Bindings] (initial t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame initial t #v[registerRegion initial .rdi 80, Stack.region initial 3680]
  rsp : stackPtr t = stackPtr initial - 312
  saved : ∀ slot ∈ savedSlots,
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 slot.2) 64 = initial.regValue slot.1
  returnAddress : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip
  registers : ∀ r ∈ [Syntax.Reg.rbp, .r13], t.regValue r = initial.regValue r
  mxcsr : t.MXCSR = initial.MXCSR
  fp87 : t.FP87_Control = initial.FP87_Control

theorem SavedEntry.frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre s boundary bytes) (entry : SavedEntry s t boundary) :
    Frame s t := by
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported entry.ready entry.agrees,
    supportedMachine_of_ready_agrees pre.machine entry.ready entry.agrees, entry.loaded,
    entry.agrees.directionFlagClear (by simp [saveComponents, pushSequenceFrame, savedRegisters]) pre.directionFlag,
    entry.agrees.grow, ?_, entry.rsp, ?_, ?_, ?_,
    entry.agrees.mxcsr (by simp [saveComponents, pushSequenceFrame, savedRegisters]),
    entry.agrees.fcw (by simp [saveComponents, pushSequenceFrame, savedRegisters])⟩
  · have frame := pushSequence_frame pre.stack (sources := savedRegisters) (offset := 0)
      (by decide) entry.agrees (by simp [Component.Covers])
    intro a ha
    apply frame a
    intro r hr
    exact ha r (by simpa using Or.inr hr)
  · intro slot member
    rw [entry.memory]
    exact savedMemory_slots s slot member
  · rw [entry.memory]
    change memLoad (memStore (memStore (memStore (memStore s.external
      (stackPtr s - 8) (s.regValue .r15)) (stackPtr s - 16) (s.regValue .r14))
      (stackPtr s - 24) (s.regValue .r12)) (stackPtr s - 32) (s.regValue .rbx))
      (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    simp only [BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact entry.agrees.read (n := 64) (r := 5) (by simp [saveComponents, pushSequenceFrame, savedRegisters])
    · exact entry.agrees.read (n := 64) (r := 13) (by simp [saveComponents, pushSequenceFrame, savedRegisters])

theorem Frame.after_effect [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {cs : List Component} (pre : DecodePre s boundary bytes)
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32])
    (registers : ∀ r ∈ ([4, 5, 13] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre.toCalleePre memory)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    ScalarFrame.loaded_of_frame pre.toCalleePre total,
    agrees.directionFlagClear hdf state.directionFlag,
    fun a ha ↦ agrees.grow a (state.allocated a ha), total,
    (agrees.read (n := 64) (r := 4) (registers _ (by simp))).trans state.rsp,
    ?_, ?_, ?_, (agrees.mxcsr hmxcsr).trans state.mxcsr, (agrees.fcw hfcw).trans state.fp87⟩
  · intro slot member
    have bound : slot.2 ≤ 32 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.Work.read pre.toCalleePre (by decide) memory bound (by omega)).trans
      (state.saved slot member)
  · have h := ScalarFrame.Work.read pre.toCalleePre (by decide) memory
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (agrees.read (n := 64) (r := 5) (registers _ (by simp))).trans
        (state.registers .rbp (by simp))
    · exact (agrees.read (n := 64) (r := 13) (registers _ (by simp))).trans
        (state.registers .r13 (by simp))

theorem Frame.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {cs : List Component} (pre : DecodePre s boundary bytes)
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (noMemory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (registers : ∀ r ∈ ([4, 5, 13] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u :=
  state.after_effect pre ready agrees (fun c hc a ha ↦ (noMemory c hc a ha).elim)
    registers hdf hmxcsr hfcw

end P256.Proofs.Sec1.Decode
