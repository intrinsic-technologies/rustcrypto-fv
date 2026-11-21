import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Header
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Output
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {n : Nat} (pre : ScalarPre s boundary cursor point)
    (state : Memory s t cursor point) (execution : ∃ fuel, Advances boundary fuel s t)
    (rip : t.RIP = 0x10b346) (rbx : t.regValue .rbx = s.regValue .rdi)
    (length : t.regValue .rax = BitVec.ofNat 64 (digits n).length)
    (values : ∀ i < 257, memLoad t.external (stackPtr s-344+BitVec.ofNat 64 i) 8 =
      BitVec.ofInt 8 (((digits n)[i]?).getD 0)) :
    ∃ u, ScalarResult s u boundary cursor point ∧ NafAt u (s.regValue .rdi) n := by
  have values' : ∀ i < 257, memLoad t.external (stackPtr t+16+BitVec.ofNat 64 i) 8 =
      BitVec.ofInt 8 (((digits n)[i]?).getD 0) := by
    have address : stackPtr t+16 = stackPtr s-344 :=
      stack_address state.rsp (offset := 16) (by decide)
    rw [address]
    exact values
  obtain ⟨u, run0, state0, rip0, rbx0, naf0⟩ := store_header pre state rip length values'
  obtain ⟨amount, v, run1, state1, rip1, naf1, cursor1, rbx1⟩ :=
    copy_naf_output pre state0 (rbx0.trans rbx) naf0 rip0
  obtain ⟨fuel, run⟩ := execution
  obtain ⟨w, result, memory⟩ := epilogue pre state1 rip1 rbx1 cursor1
    ⟨fuel+1+amount, (run.trans run0).trans run1⟩
  refine ⟨w, result, naf1.of_copy ?_⟩
  intro i hi
  rw [memory]

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
