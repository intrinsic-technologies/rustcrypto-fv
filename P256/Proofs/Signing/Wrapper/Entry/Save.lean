import P256.Spec.Program.Functions
import P256.Proofs.Program.CallPre
import P256.Proofs.Program.PushSequenceFrame
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedMemory (s : RamState) : Ram := pushSequenceMemory s s.external 0 [5, 15, 14, 13, 12, 3]

def saveComponents (s : RamState) : List Component :=
  pushSequenceFrame s 0 [5, 15, 14, 13, 12, 3] ++ [.reg 4, .flags, .rip]

structure SavedEntry [Bindings] (initial s : RamState) : Prop where
  execution : Advances (returnBoundary initial) 7 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x102361
  rsp : stackPtr s = stackPtr initial - 520
  memory : s.external = savedMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s

theorem save_correct [bindings : Bindings] {s : RamState} {secret message : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (h : ValidCallWithSlices signingKeyTrySign s [secret, message] slices) :
    ∃ t, SavedEntry s t := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x2350) [5, 15, 14, 13, 12, 3]
      h.stackAvailable.1 (call_stack_avoids h) (outer_boundary h hm hb)
      (readyToStep hm hb) h.programLoaded (fun _ ha ↦ ha) (by simp)
      h.atEntryPoint (by decide) (by decide) (by decide) (fun _ _ ↦ rfl)
      (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x235a 472 readyU loadedU (outer_boundary h hm hb) ripU
      (by decide) (by decide +kernel)
  refine ⟨t, ⟨runU.trans runT, readyT, loadedT, ripT, ?_, memoryT.trans memoryU,
    agreesU.trans agreesT⟩⟩
  rw [rspT, rspU, BitVec.sub_sub]
  rfl

theorem saved_frame [Bindings] {s t : RamState}
    (stack : Stack.Valid s signingKeyTrySign.minStackBytes) (saved : SavedEntry s t) :
    MemoryWriteFrame s t (wrapperRegions signingKeyTrySign s) := by
  apply saved.agrees.memoryWriteFrame
  intro c hc a hv
  rcases List.mem_append.mp hc with hc | hc
  · exact ⟨callStack signingKeyTrySign s, by simp [wrapperRegions],
      stack_contains_callStack (pushSequenceFrame_covers [5, 15, 14, 13, 12, 3] stack
        (by decide) hc hv)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact hv.elim

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]

theorem savedMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (member : entry ∈ savedRegisters) :
    memLoad (savedMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [savedMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

theorem savedMemory_return (s : RamState) :
    memLoad (savedMemory s) (stackPtr s) 64 = (returnBoundary s).rip := by
  change memLoad (savedMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  simp only [savedMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
  repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]


end P256.Proofs.Signing.Wrapper.Entry
