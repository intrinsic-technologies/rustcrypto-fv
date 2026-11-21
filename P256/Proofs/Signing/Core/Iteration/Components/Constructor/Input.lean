import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Call

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
theorem input_scalar_of_frame {reg : X86.Syntax.Reg} {d : Nat}
    (bounded : (registerRegion s reg 32).Bounded)
    (outputApart : (registerRegion s reg 32).Disjoint (registerRegion s .rdi 72))
    (stackApart : (registerRegion s reg 32).Disjoint (Stack.region s 512))
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdi 72, Stack.region s 512])
    (value : Nat256At s (s.regValue reg) d) : Nat256At t (s.regValue reg) d := by
  refine ⟨value.1, fun i hi => ?_⟩
  rw [frame _]
  · exact value.2 i hi
  · intro region hr hin
    have hc := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
    have hr' : region = registerRegion s .rdi 72 ∨ region = Stack.region s 512 := by
      simpa using hr
    rcases hr' with rfl | rfl
    · exact outputApart _ hc hin
    · exact stackApart _ hc hin

theorem Frame.left_scalar (pre : ConstructorPre s boundary) (state : Frame s t) {d : Nat}
    (value : Nat256At s (s.regValue .rsi) d) : Nat256At t (s.regValue .rsi) d :=
  input_scalar_of_frame pre.inputBounded
    (pre.separation (0 : Fin 3) (1 : Fin 3) (by decide))
    (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)) state.frame value

theorem Frame.right_scalar (pre : ConstructorPre s boundary) (state : Frame s t) {d : Nat}
    (value : Nat256At s (s.regValue .rdx) d) : Nat256At t (s.regValue .rdx) d :=
  input_scalar_of_frame pre.rightBounded pre.rightOutput pre.rightStack state.frame value

theorem input_scalar_call {target : RamState → BitVec 64} {ret : BitVec 64}
    {reg : X86.Syntax.Reg} {d : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (bounded : (registerRegion s reg 32).Bounded)
    (apart : (registerRegion s reg 32).Disjoint (Stack.region s 512))
    (effect : (callEffect target ret t).Holds t u)
    (value : Nat256At t (s.regValue reg) d) : Nat256At u (s.regValue reg) d := by
  refine ⟨value.1, fun i hi => ?_⟩
  rw [effect.agrees.memoryWriteFrame (constructor_call_writes pre state) _]
  · exact value.2 i hi
  · intro region hr hin
    have hregion : region = Stack.region s 512 := by simpa using hr
    subst region
    exact apart _ (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi) hin

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
