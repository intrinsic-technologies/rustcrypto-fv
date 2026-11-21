import P256.Spec
import P256.Proofs.Program.CallPre
import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (BitVec 4) := [15, 14, 3]

def savedMemory (s : RamState) : Ram := pushSequenceMemory s s.external 0 savedRegisters

def saveComponents (s : RamState) : List Component :=
  pushSequenceFrame s 0 savedRegisters ++ [.reg 4, .flags, .rip]

structure SavedEntry [Bindings] (initial s : RamState) : Prop where
  execution : Advances (returnBoundary initial) 4 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x1017dc
  rsp : stackPtr s = stackPtr initial - 232
  memory : s.external = savedMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s

theorem save_correct [bindings : Bindings] {s : RamState} {bytes : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (h : ValidCallWithSlices publicKeyFromSec1Bytes s [bytes] slices) :
    ∃ t, SavedEntry s t := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    push_sequence savedRegisters h.stackAvailable.1 (call_stack_avoids h)
      (outer_boundary h hm hb) (readyToStep hm hb) h.programLoaded (fun _ ha => ha)
      (offset := 0) (codeOffset := 0x17d0) (by simp) h.atEntryPoint
      (by decide) (by decide) (by decide) (fun _ _ => rfl) (by simp only [savedRegisters, PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x17d5 208 readyU loadedU (outer_boundary h hm hb)
      ripU (by decide) (by decide +kernel)
  refine ⟨t, ⟨runU.trans runT, readyT, loadedT, ripT, ?_,
    memoryT.trans memoryU, agreesU.trans agreesT⟩⟩
  rw [rspT, rspU, BitVec.sub_sub]
  rfl

theorem saved_frame [Bindings] {s t : RamState}
    (stack : Stack.Valid s publicKeyFromSec1Bytes.minStackBytes) (saved : SavedEntry s t) :
    MemoryWriteFrame s t (wrapperRegions publicKeyFromSec1Bytes s) := by
  apply saved.agrees.memoryWriteFrame
  intro c hc a hv
  simp only [saveComponents, pushSequenceFrame, savedRegisters, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals refine ⟨callStack publicKeyFromSec1Bytes s, by simp [wrapperRegions], ?_⟩
  all_goals exact stack_component_within stack (by decide) (by decide) hv

end P256.Proofs.Sec1.Wrapper
