import Sha1.Proofs.Compress.Routine.Public
import Sha1.Proofs.Compress.Routine.Prologue
import Sha1.Proofs.Compress.Routine.Next
import Sha1.Proofs.Compress.Routine.Finish
import Sha1.Proofs.Compress.Routine.Empty

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem execution (hBlock : Machine.BlockCorrect) (bindings : Bindings)
    (c : Context) (hv : c.Valid bindings) :
    ∃ n t, @Returns bindings (returnBoundary c.initial) n c.initial t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  by_cases hz : c.count = 0
  · exact empty_execution bindings c hv hz
  · exact execution_of_parts hBlock prologueCorrect nextCorrect finishCorrect bindings c hv
      (Nat.pos_of_ne_zero hz)

theorem correct (hBlock : Machine.BlockCorrect)
    {initial : RamState} {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (bindings : Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial H blocks) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (Hasher.stateBytes
          ((SHA2.SHA256.parse (SHA2.bytesToBits blocks)).foldl SHA1.compress H)) := by
  exact correct_of_parts hBlock prologueCorrect nextCorrect finishCorrect bindings
    hBindings hMachine hCall

theorem execution_advance (hBlock : Machine.BlockCorrect) (boundary : ReturnBoundary)
    (bindings : Bindings) (c : Context) (hv : c.Valid bindings)
    (hBoundary : Machine.OutsideCompression boundary.rip)
    (hDifferent : boundary.rip ≠ (returnBoundary c.initial).rip) :
    ∃ n t, @Advances bindings boundary n c.initial t ∧
      @ReadyToStep bindings t ∧ Result c t := by
  letI := bindings
  by_cases hz : c.count = 0
  · exact empty_execution_advance bindings boundary c hv hBoundary hDifferent hz
  · have hn : 0 < c.count := Nat.pos_of_ne_zero hz
    obtain ⟨n, s, hAdvance, hReady, hCode, hRip, hAt, _⟩ :=
      prologueAdvanceCorrect bindings boundary c hv hBoundary hn
    rw [← c.state_zero] at hAt
    obtain ⟨m, t, hRun, hReady', hResult⟩ :=
      finishFrom_rel (hBlock := hBlock) (bindings := bindings)
        (boundary := boundary) (c := c) (hv := hv) (hOutside := hBoundary)
        (R := fun n s t ↦ @Advances bindings boundary n s t) (Q := Result c)
        (nextAdvanceCorrect bindings boundary c hv hBoundary)
        (finishAdvanceCorrect bindings boundary c hv hBoundary hDifferent)
        (fun ha hb ↦ ha.trans hb) 0 hn s hReady hCode hRip hAt
    exact ⟨n + m, t, hAdvance.trans hRun, hReady', hResult⟩

end Sha1.Proofs.Compress.Routine
