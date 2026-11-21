import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.Memory
import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.State
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

export P256.Proofs.SignatureFromDer.Fixed.Finish (nat256_after_stack_store output_word_preserved Payload)

theorem after_stack_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {fuel off : Nat} (pre : CalleePre s boundary 0x109890 32 72 512)
    (state : Stage s t boundary) (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (frame : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 off) 8, .rip] t u)
    (bound : off + 8 ≤ 192) : Stage s u boundary := by
  apply state.after pre run ready frame
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨workRegion s, by simp, ?_⟩
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)] at ha
      exact Program.ScalarFrame.Work.contains pre (by omega) (by omega) ha
    · exact ha.elim
  · exact (frame.read (n := 64) (r := 4) (by simp)).trans state.rsp
  · simp

theorem after_output_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {fuel off : Nat} (pre : CalleePre s boundary 0x109890 32 72 512)
    (state : Stage s t boundary) (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (frame : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 off) 8, .rip] t u)
    (bound : off + 8 ≤ 72) : Stage s u boundary := by
  apply state.after pre run ready frame
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨registerRegion s .rdi 72, by simp, output_contains pre bound ha⟩
    · exact ha.elim
  · exact (frame.read (n := 64) (r := 4) (by simp)).trans state.rsp
  · simp


end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
