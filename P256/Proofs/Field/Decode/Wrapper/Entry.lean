import P256.Proofs.Field.Interface
import P256.Proofs.Program.PushSequenceFrame
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Field.Decode.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) :=
  CalleePre s boundary 0x114240 32 32 40

def sources : List (BitVec 4) := [15, 14, 13, 12, 3]

def prologueComponents (s : RamState) := pushSequenceFrame s 0 sources

def prologueMemory (s : RamState) := pushSequenceMemory s s.external 0 sources

structure Entry [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 5 s t
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = 0x114249
  rsp : stackPtr t = stackPtr s - 40
  memory : t.external = prologueMemory s
  agrees : AgreesExcept (prologueComponents s) s t

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : ∃ t, Entry s t boundary := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x14240)
      sources pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp) pre.rip (by decide) (by decide)
      (by simp [sources]) (by intros; rfl) (by simp only [sources, PushSequenceCode]; decide +kernel)
  exact ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩

theorem entry_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (entry : Entry s t boundary) :
    MemoryWriteFrame s t #v[Stack.region s 40] := by
  apply entry.agrees.memoryWriteFrame
  intro c hc a ha
  exact ⟨Stack.region s 40, by simp,
    pushSequenceFrame_covers sources pre.stack (by decide) hc ha⟩

theorem input_unchanged [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (entry : Entry s t boundary) {x : Nat}
    (value : Field.MontgomeryAt s (s.regValue .rsi) x) :
    Field.MontgomeryAt t (t.regValue .rsi) x := by
  have si : t.regValue .rsi = s.regValue .rsi :=
    entry.agrees.read (n := 64) (r := 6) (by simp [prologueComponents, sources, pushSequenceFrame])
  rw [si]
  refine ⟨value.1, value.2.1, ?_⟩
  intro i hi
  rw [entry_frame pre entry _]
  · exact value.2.2 i hi
  · intro r hr hin
    have eq : r = Stack.region s 40 := by simpa using hr
    subst r
    exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _
      (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi) hin

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (entry : Entry s t boundary) :
    MemReadable t (t.regValue .rsi) 32 := by
  have si : t.regValue .rsi = s.regValue .rsi :=
    entry.agrees.read (n := 64) (r := 6) (by simp [prologueComponents, sources, pushSequenceFrame])
  rw [si]
  exact readable_of_grow
    (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _))
    entry.agrees.grow

end P256.Proofs.Field.Decode.Wrapper
