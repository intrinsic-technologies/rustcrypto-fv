import P256.Proofs.Generate.Zero.Interface
import P256.Proofs.Program.Push
import P256.Proofs.Program.ScalarFrame.CallStep

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64}

theorem prefix_writes (pre : CalleePre s boundary entry 32 32 32) :
    WritesWithin (prefixClobbers s) #v[Stack.region s 32] := by
  intro c hc address cover
  simp only [prefixClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals refine ⟨Stack.region s 32, by simp, ?_⟩
  · exact ScalarFrame.stack_contains pre (offset := 8) (by decide) (by decide) cover
  · exact ScalarFrame.stack_contains pre (offset := 16) (by decide) (by decide) cover

theorem prefix_loaded (pre : CalleePre s boundary entry 32 32 32)
    (agrees : AgreesExcept (prefixClobbers s) s t) : ProgramLoaded t := by
  have memory := agrees.memoryWriteFrame (prefix_writes pre)
  intro a b fetch
  rw [memory a]
  · exact pre.loaded a b fetch
  · intro region hr ha
    have eq : region = Stack.region s 32 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a ha (.inl ⟨b, fetch⟩)

theorem prefix_input (pre : CalleePre s boundary entry 32 32 32)
    (agrees : AgreesExcept (prefixClobbers s) s t)
    {reg : Syntax.Reg} {x : Nat}
    (bounded : (registerRegion s reg 32).Bounded)
    (apart : (registerRegion s reg 32).Disjoint (Stack.region s 32))
    (input : Nat256At s (s.regValue reg) x) : Nat256At t (s.regValue reg) x := by
  refine ⟨input.1, fun i hi => ?_⟩
  have memory := agrees.memoryWriteFrame (prefix_writes pre)
  rw [memory]
  · exact input.2 i hi
  · intro region hr ha
    have eq : region = Stack.region s 32 := by simpa using hr
    subst region
    exact apart _ (memoryRegion_contains_add bounded (len := 32)
      (Nat.le_refl _) (Nat.le_refl _) hi) ha

end P256.Proofs.Generate.Zero
