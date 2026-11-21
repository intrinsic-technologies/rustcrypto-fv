import P256.Proofs.Projective.Multiply.Machine.Radix.State

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem State.after_stack {u : RamState} {offset offset' : BitVec 64} {cs : List Component}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t offset)
    (ready : ReadyToStep u) (ag : AgreesExcept cs t u)
    (regs : ∀ c ∈ cs, c.isMem = false → c ∈ registers)
    (memory : ∀ p n, Component.mem p n ∈ cs →
      ∃ off, off ≤ 136 ∧ n+8 ≤ off ∧ p = stackPtr s-BitVec.ofNat 64 off)
    (rsp : stackPtr u = stackPtr s-offset') : State s u offset' := by
  apply state.after pre ready ag regs ?_ rsp
  intro c hc a ha
  cases c with
  | mem p n =>
    obtain ⟨off,ho,hl,rfl⟩ := memory p n hc
    exact ⟨workRegion s,by simp,ScalarFrame.Work.contains pre ho hl ha⟩
  | _ => exact ha.elim

theorem State.stack_readable {frameOffset offset len : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t (BitVec.ofNat 64 frameOffset))
    (hframe : frameOffset ≤ 136) (bound : offset+len ≤ frameOffset) :
    MemReadable t (stackPtr t+BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address state.rsp (by omega) (by omega)]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.agrees.grow

theorem State.stack_writable {frameOffset offset len : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t (BitVec.ofNat 64 frameOffset))
    (hframe : frameOffset ≤ 136) (bound : offset+len ≤ frameOffset) (positive : 0<len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (stackPtr t+BitVec.ofNat 64 offset) len := by
  have readable := state.stack_readable pre hframe bound
  refine ⟨readable,tables_of_not_reserved positive readable.low ?_⟩
  intro i hi hin
  apply pre.avoids (Stack.region s 136) (by simp) _ ?_ (.inr hin)
  rw [ScalarFrame.scalar_stack_address state.rsp (by omega) (by omega)]
  exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i,hi,rfl⟩

theorem State.stack_code {frameOffset offset len codeOffset codeLen : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t (BitVec.ofNat 64 frameOffset))
    (hframe : frameOffset ≤ 136) (bound : offset+len ≤ frameOffset)
    (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr t+BitVec.ofNat 64 offset) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 136) (by simp)
    (stackPtr t+BitVec.ofNat 64 offset+BitVec.ofNat 64 i) ?_ (.inl ?_)
  · rw [ScalarFrame.scalar_stack_address state.rsp (by omega) (by omega)]
    exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i,hi,rfl⟩
  · rw [he,BitVec.add_assoc,←BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

end P256.Proofs.Projective.Multiply.Machine.Radix
