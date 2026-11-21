import P256.Proofs.HMAC.Interface
import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev saveSources : List (BitVec 4) := [5, 15, 14, 13, 12, 3]

abbrev saveMemory (s : RamState) := pushSequenceMemory s s.external 0 saveSources

abbrev saveComponents (s : RamState) :=
  pushSequenceFrame s 0 saveSources ++ [.reg 4, .flags, .rip]

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre s boundary 0x100f10 168 672) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x100f21 ∧ stackPtr t = stackPtr s - 328 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveComponents s) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0xf10) saveSources
      pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp) pre.rip (by decide) (by decide) (by decide) (fun _ _ => rfl)
      (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0xf1a 280 ready loaded pre.outerBoundary rip (by decide)
      (by decide +kernel)
  refine ⟨t, run.trans runT, readyT, loadedT, ripT, ?_, memoryT.trans memory,
    agrees.trans agreesT⟩
  change stackPtr t = stackPtr u - 280 at rspT
  rw [rspT, rsp, BitVec.sub_sub]
  rfl

end P256.Proofs.HMAC.Finalize
