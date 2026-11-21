import P256.Proofs.Projective.Multiply.Machine.Lookup.Call.Site

set_option autoImplicit false

open P256.Proofs.Program (CalleePre StackCallLayout stack_region_end)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Proofs.Field (MontgomeryAt)
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) {offset : Nat} (bound : offset < 768) :
    (registerRegion s .rsi 768).Contains (s.regValue .rsi + BitVec.ofNat 64 offset).toNat := by
  have bounded : (s.regValue .rsi).toNat + 768 < 2^32 := pre.inputBounded
  change (s.regValue .rsi).toNat ≤ _ ∧ _ < (s.regValue .rsi).toNat + 768
  rw [toNat_add_ofNat _ _ (by omega)]
  constructor <;> omega

theorem FrameState.input_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {stackOffset : BitVec 64} (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (state : FrameState s t stackOffset) {offset : Nat} (bound : offset < 768) :
    t.external[s.regValue .rsi + BitVec.ofNat 64 offset]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 offset]? := by
  apply state.frame
  intro region hr hin
  have hr' : region = registerRegion s .rdi 96 ∨ region = Stack.region s 496 := by
    simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _
      (input_contains pre bound) hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _
      (input_contains pre bound) hin

theorem FrameState.input_montgomery [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {stackOffset : BitVec 64} (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (state : FrameState s t stackOffset) {offset x : Nat} (bound : offset + 32 ≤ 768)
    (input : MontgomeryAt s (s.regValue .rsi + BitVec.ofNat 64 offset) x) :
    MontgomeryAt t (s.regValue .rsi + BitVec.ofNat 64 offset) x := by
  refine ⟨input.1, input.2.1, ?_⟩
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, state.input_byte pre (by omega)]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact input.2.2 i hi

theorem binary_pre_external [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve : Nat}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (state : FrameState s t 368) (layout : StackCallLayout 496 32 32 reserve)
    (layoutStack : layout.stackOffset = 368)
    (rightOffset : Nat) (rightBound : rightOffset + 32 ≤ 768)
    (rip : t.RIP = entry)
    (input : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 layout.inputOffset)
    (right : t.regValue .rdx = s.regValue .rsi + BitVec.ofNat 64 rightOffset)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary t).rip) :
    P256.Proofs.Field.BinaryFieldPre t boundary entry reserve := by
  have base := CalleePre.of_stack pre layout state.bindingsSupported state.machine state.directionFlag
    state.loaded state.allocated rip (layoutStack ▸ state.rsp) input output ret
  have bounds := P256.Proofs.Program.stack_bounds pre.stack
  have capacity := layout.capacity
  rw [layoutStack] at capacity
  have outputAbove := layout.outputAbove
  rw [layoutStack] at outputAbove
  have outputEnd := layout.outputEnd
  have inputBounded : (s.regValue .rsi).toNat + 768 < 2^32 := pre.inputBounded
  have hr : (t.regValue .rdx).toNat = (s.regValue .rsi).toNat + rightOffset := by
    rw [right, toNat_add_ofNat _ _ (by omega)]
  have ho : (t.regValue .rdi).toNat = (stackPtr s).toNat - layout.outputOffset := by
    rw [output]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)
  have hs : (stackPtr t).toNat = (stackPtr s).toNat - 368 := by
    rw [state.rsp]
    exact P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)
  have rightSub : ∀ a, (registerRegion t .rdx 32).Contains a →
      (registerRegion s .rsi 768).Contains a := by
    intro a ha
    change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat + 32 at ha
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 768
    rw [hr] at ha
    constructor <;> omega
  refine { base with
    rightBounded := ?_
    rightAllocated := ?_
    rightOutput := ?_
    rightStack := ?_ }
  · change (t.regValue .rdx).toNat + 32 < 2^32
    rw [hr]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.inputAllocated a (rightSub a.toNat ha))))
  · intro a ha hb
    apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (rightSub a ha)
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + 32 at hb
    rw [ho] at hb
    change (stackPtr s).toNat - 496 ≤ a ∧
      a < (Stack.region s 496).start + (Stack.region s 496).size
    rw [stack_region_end]
    constructor <;> omega
  · intro a ha hb
    apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) a (rightSub a ha)
    change (stackPtr t).toNat - reserve ≤ a ∧
      a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
    rw [stack_region_end, hs] at hb
    change (stackPtr s).toNat - 496 ≤ a ∧
      a < (Stack.region s 496).start + (Stack.region s 496).size
    rw [stack_region_end]
    constructor <;> omega

end P256.Proofs.Projective.Multiply.Machine.Lookup
