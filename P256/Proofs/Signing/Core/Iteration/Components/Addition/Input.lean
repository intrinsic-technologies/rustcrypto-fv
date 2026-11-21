import P256.Proofs.Signing.Core.Iteration.Components.Addition.Initialize
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Prologue

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.Program (memoryRegion_contains_add)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_preserved [Bindings] {s t : RamState}
    {r : Syntax.Reg} {a : Nat}
    (state : FrameState s t) (input : Nat256At s (s.regValue r) a)
    (bounded : (registerRegion s r 32).Bounded)
    (output : (registerRegion s r 32).Disjoint (registerRegion s .rdi 32))
    (stack : (registerRegion s r 32).Disjoint (Stack.region s 64)) :
    Nat256At t (s.regValue r) a := by
  refine ⟨input.1, ?_⟩
  intro i hi
  rw [state.frame _]
  · exact input.2 i hi
  · intro region hr hin
    have inside := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi
    have regionEq : region = registerRegion s .rdi 32 ∨ region = Stack.region s 64 := by
      simpa using hr
    rcases regionEq with rfl | rfl
    · exact output _ inside hin
    · exact stack _ inside hin

theorem start [Bindings] {s : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : BinaryFieldPre s boundary 0x113310 64)
    (left : Nat256At s (s.regValue .rsi) a)
    (right : Nat256At s (s.regValue .rdx) b) :
    ∃ t, Advances boundary 9 s t ∧ FrameState s t ∧ t.RIP = 0x11392e ∧
      t.regValue .rsi = s.regValue .rsi ∧ t.regValue .rdx = s.regValue .rdx ∧
      t.regValue .rdi = s.regValue .rdi ∧ t.regValue .rcx = 0x2025e0 ∧
      Nat256At t (t.regValue .rsi) a ∧ Nat256At t (t.regValue .rdx) b := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees, rcx⟩ := prologue pre.toCalleePre
  have state := prologue_frame pre.toCalleePre ready loaded rsp memory agrees
  have rsi : t.regValue .rsi = s.regValue .rsi :=
    agrees.read (n := 64) (r := 6) (by simp [P256.Proofs.Program.saveFrame])
  have rdx : t.regValue .rdx = s.regValue .rdx :=
    agrees.read (n := 64) (r := 2) (by simp [P256.Proofs.Program.saveFrame])
  refine ⟨t, run, state, rip, rsi, rdx, ?_, rcx, ?_, ?_⟩
  · exact agrees.read (n := 64) (r := 7) (by simp [P256.Proofs.Program.saveFrame])
  · rw [rsi]
    exact input_preserved state left pre.inputBounded
      (pre.separation (0 : Fin 3) (1 : Fin 3) (by decide))
      (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide))
  · rw [rdx]
    exact input_preserved state right pre.rightBounded pre.rightOutput pre.rightStack

end P256.Proofs.Signing.Core.Iteration.Components.Addition
