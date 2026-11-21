import P256.Proofs.Verifying.Combination.Naf.Iterator.Interface
import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize.Prologue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program (push_exists)

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {reserve : Nat} (pre : CalleePre s boundary 0x1181b0 0 40 reserve)
    (reserved : 24 ≤ reserve) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1181b4 ∧ stackPtr t = stackPtr s - 24 ∧
      t.external = Initialize.saveMemory s ∧ AgreesExcept (Initialize.saveFrame s) s t := by
  obtain ⟨s1, run1, ready1, loaded1, rip1, sp1, ag1, mem1⟩ :=
    push_exists pre.stack (pre.avoids (Stack.region s reserve) (by simp)) pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      14 0 0x181b0 (by simp only [BitVec.sub_zero]) pre.rip (by omega) (by decide)
      (by decide +kernel) (by decide +kernel)
  obtain ⟨s2, run2, ready2, loaded2, rip2, sp2, a2, mem2⟩ :=
    push_exists pre.stack (pre.avoids (Stack.region s reserve) (by simp)) pre.outerBoundary ready1 loaded1 ag1.grow 3 8 0x181b2 sp1 rip1
      (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  have ag2 := ag1.trans a2
  obtain ⟨s3, run3, ready3, loaded3, rip3, sp3, a3, mem3⟩ :=
    push_exists pre.stack (pre.avoids (Stack.region s reserve) (by simp)) pre.outerBoundary ready2 loaded2 ag2.grow 0 16 0x181b3 sp2 rip2
      (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  refine ⟨s3, (run1.trans run2).trans run3, ready3, loaded3, rip3, sp3, ?_, ?_⟩
  · have v1 : (Operand.reg 14 : Operand 64).read s = s.regValue .r14 := rfl
    have v2 : (Operand.reg 3 : Operand 64).read s1 = s.regValue .rbx := ag1.read (by simp)
    have v3 : (Operand.reg 0 : Operand 64).read s2 = s.regValue .rax := ag2.read (by simp)
    rw [mem3, mem2, mem1]
    simp only [show BitVec.setWidth 5 (14 : BitVec 4) = (14 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (3 : BitVec 4) = (3 : BitVec 5) from rfl,
      show BitVec.setWidth 5 (0 : BitVec 4) = (0 : BitVec 5) from rfl, v1, v2, v3]
    rfl
  · apply (ag2.trans a3).mono
    simp only [Initialize.saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((h | h) | h) <;> rcases h with rfl | rfl | rfl <;> simp

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
