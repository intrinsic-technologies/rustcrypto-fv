import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Start
import P256.Proofs.Verifying.Combination.Naf.Machine.Iteration

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem recode_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (zeroes : Bytes s.external (s.regValue .rdi) 257 (fun _ => 0)) :
    ∃ t, CalleeResult s t boundary 257 168 ∧
      t.regValue .rax = BitVec.ofNat 64 (digits n).length ∧
      ∀ i < 257, memLoad t.external (s.regValue .rdi + BitVec.ofNat 64 i) 8 =
        BitVec.ofInt 8 (((digits n)[i]?).getD 0) := by
  obtain ⟨fuel0, t, run0, state⟩ := start_recoding pre input zeroes
  obtain ⟨fuel1, u, c, ds, run1, finished⟩ := loop_of_progress (iteration pre input) state
  exact finished.correct pre ⟨fuel0+fuel1,run0.trans run1⟩

end P256.Proofs.Verifying.Combination.Naf.Machine
