import P256.Proofs.Verifying.Combination.Naf.Machine.Finish.Select
import P256.Proofs.Verifying.Combination.Naf.Machine.Finish.Append
import P256.Proofs.Verifying.Combination.Naf.Machine.Finish.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish_recoding [Bindings] {s t : RamState} {boundary : ReturnBoundary} {ds : List Int} {c : Nat}
    (pre : Pre s boundary) (state : FrameState s t) (rip : t.RIP = 0x10f4da)
    (carry : c ≤ 1) (bound : ds.length ≤ 256)
    (r13 : t.regValue .r13 = BitVec.ofNat 64 c) (r14 : t.regValue .r14 = BitVec.ofNat 64 ds.length)
    (length : memLoad t.external (stackPtr s-136) 64 = 257)
    (pointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi)
    (output : DigitsAt t (s.regValue .rdi) ds) (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 257 168 ∧ u.regValue .rax = BitVec.ofNat 64 (ds.length+c) ∧
      DigitsAt u (s.regValue .rdi) (ds ++ if c=0 then [] else [1]) := by
  obtain ⟨u, run0, state0, rip0, agrees0⟩ := finish_select pre state rip carry r13
  have memory0 : u.external = t.external := agrees0.external (by simp [Component.Covers])
  have output0 := digits_of_external_eq output memory0
  have index0 : u.regValue .r14 = BitVec.ofNat 64 ds.length :=
    (agrees0.read (n := 64) (r := 14) (by simp)).trans r14
  obtain ⟨fuel, run⟩ := execution
  by_cases zero : c=0
  · have rip0' : u.RIP = 0x10f4f5 := by simpa only [ite_eq_left zero] using rip0
    obtain ⟨v, result, memory, value⟩ := finish_epilogue pre.toCalleePre state0 rip0'
      ⟨fuel+2, run.trans run0⟩
    refine ⟨v, result, ?_, ?_⟩
    · simpa only [zero, Nat.add_zero] using value.trans index0
    · simpa only [ite_eq_left zero, List.append_nil] using digits_of_external_eq output0 memory
  · have one : c=1 := by omega
    have rip0' : u.RIP = 0x10f4df := by simpa only [ite_eq_right zero] using rip0
    obtain ⟨v, run1, state1, rip1, index1, output1⟩ := finish_append pre state0 rip0' bound index0
      (by rw [memory0]; exact length) (by rw [memory0]; exact pointer) output0
    obtain ⟨w, result, memory, value⟩ := finish_epilogue pre.toCalleePre state1 rip1
      ⟨fuel+2+6, (run.trans run0).trans run1⟩
    refine ⟨w, result, ?_, ?_⟩
    · simpa only [one] using value.trans index1
    · simpa only [ite_eq_right zero] using digits_of_external_eq output1 memory

end P256.Proofs.Verifying.Combination.Naf.Machine
