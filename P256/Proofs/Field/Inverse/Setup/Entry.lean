import P256.Proofs.Field.Inverse.Interface
import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

abbrev saveSources : List (BitVec 4) := [5, 3]

abbrev entryMemory (s : RamState) := pushSequenceMemory s s.external 0 saveSources

abbrev entryComponents (s : RamState) :=
  pushSequenceFrame s 0 saveSources ++ [.reg 4, .flags, .rip]

theorem inverse_entry_steps [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x114099 ∧ stackPtr t = stackPtr s - 168 ∧
      t.external = entryMemory s ∧ AgreesExcept (entryComponents s) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x14090) saveSources
      pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp) pre.rip (by decide) (by decide) (by decide) (fun _ _ => rfl)
      (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x14092 152 ready loaded pre.outerBoundary rip (by decide)
      (by decide +kernel)
  refine ⟨t, run.trans runT, readyT, loadedT, ripT, ?_, memoryT.trans memory,
    agrees.trans agreesT⟩
  change stackPtr t = stackPtr s - 168
  change stackPtr t = stackPtr u - 152 at rspT
  rw [rspT, rsp, BitVec.sub_sub]
  rfl

end P256.Proofs.Field.Inverse
