import P256.Proofs.Nonce.Initialize.Interface
import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev saveSources : List (BitVec 4) := [5, 15, 14, 13, 12, 3]

abbrev saveMemory (s : RamState) := pushSequenceMemory s s.external 0 saveSources

abbrev saveComponents (s : RamState) :=
  pushSequenceFrame s 0 saveSources ++ [.reg 4, .flags, .rip]

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre s boundary orderAddress) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1077a1 ∧ stackPtr t = stackPtr s - 280 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveComponents s) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x7790) saveSources
      pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp) pre.rip (by decide) (by decide) (by decide) (fun _ _ => rfl)
      (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x779a 232 ready loaded pre.outerBoundary rip (by decide)
      (by decide +kernel)
  refine ⟨t, run.trans runT, readyT, loadedT, ripT, ?_, memoryT.trans memory,
    agrees.trans agreesT⟩
  change stackPtr t = stackPtr u - 232 at rspT
  rw [rspT, rsp, BitVec.sub_sub]
  rfl

end P256.Proofs.Nonce.Initialize
