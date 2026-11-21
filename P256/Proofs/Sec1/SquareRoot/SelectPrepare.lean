import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.HMAC.Key.Frame
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Field.Preserve
import P256.Proofs.Sec1.SquareRoot.SelectZero
import P256.Proofs.Sec1.SquareRoot.SelectSetup
import P256.Proofs.Sec1.SquareRoot.Representation

set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem select_zero_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (effect : (selectZeroEffect t).Holds t u) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready effect.agrees ?_ ?_, ?_⟩
  · apply effect.agrees.memoryWriteFrame
    intro c hc a hcov
    simp only [selectZeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
    all_goals
      obtain ⟨i,hi,rfl⟩ := hcov
      rw [state.stack_address]
      simp only [BitVec.reduceSub]
      exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩
  · intro r hr
    simp [selectZeroEffect, Effect.components]
  · exact (effect.agrees.read (r := 4) (n := 64) (by simp [selectZeroEffect, Effect.components])).trans state.rsp

theorem select_zero_copy [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {beta : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (effect : (selectZeroEffect t).Holds t u) (input : MontgomeryAt t (stackPtr s-576) beta) :
    MontgomeryAt u (stackPtr s-576) beta := by
  apply Field.MontgomeryAt.of_bytes_eq input
  intro i hi
  apply effect.agrees.byte
  intro c hc hcov
  simp only [selectZeroEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  all_goals
    obtain ⟨j,hj,he⟩ := hcov
    rw [state.stack_address] at he
    simp only [BitVec.reduceSub] at he
  · exact stack_sub_apart pre.stack (a := 544) (b := 576) (by decide) (by decide)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 536) (b := 576) (by decide) (by decide)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 528) (b := 576) (by decide) (by decide)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 520) (b := 576) (by decide) (by decide)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 512) (b := 576) (by decide) (by decide)
      (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm

theorem select_zero_montgomery [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (effect : (selectZeroEffect t).Holds t u) : MontgomeryAt u (stackPtr s-536) 0 := by
  have alloc : ∀ i < 32, (u.external[stackPtr s-536+BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    exact effect.agrees.grow _ (state.allocated _ ((stack_sub_readable pre.stack
      (offset := 536) (len := 32) (by decide) (by decide)).mem i hi))
  have words : ∀ j < 4, memLoad u.external (stackPtr s-536+BitVec.ofNat 64 (8*j)) 64=0 := by
    have hw := effect.writes
    change _ ∧ (Operand.mem ((Operand.reg 4 : Operand 64).read t+48) : Operand 64).read u = 0 ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read t+56) : Operand 64).read u = 0 ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read t+64) : Operand 64).read u = 0 ∧
      (Operand.mem ((Operand.reg 4 : Operand 64).read t+72) : Operand 64).read u = 0 at hw
    have hs : (Operand.reg 4 : Operand 64).read t = stackPtr s - 584 := state.rsp
    rw [hs] at hw
    intro j hj
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    all_goals change (Operand.mem _ : Operand 64).read u = _
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.2.2
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i hi
  have bytes : Bytes u.external (stackPtr s-536+BitVec.ofNat 64 (8*(i/8))) 8 (storedByte (0 : BitVec 64)) := by
    rw [← words (i/8) (by omega)]
    apply Bytes.of_memLoad (n := 64)
    intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact alloc _ (by omega)
  have h := bytes (i%8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod] at h
  simpa [storedByte] using h

structure SelectCallState [Bindings] (s t : RamState) (beta : Nat) (select : Bool) : Prop extends FrameState s t where
  rip : t.RIP=0x114594
  rsi : t.regValue .rsi=4
  rcx : t.regValue .rcx=4
  rdi : t.regValue .rdi=stackPtr s-536
  rdx : t.regValue .rdx=stackPtr s-576
  r8 : t.regValue .r8=if select then 1 else 0
  rbp : t.regValue .rbp=if select then 1 else 0
  zero : MontgomeryAt t (stackPtr s-536) 0
  candidate : MontgomeryAt t (stackPtr s-576) beta

theorem select_prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {beta : Nat} {select : Bool}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP=0x114552) (rax : t.regValue .rax=if select then 1 else 0)
    (candidate : MontgomeryAt t (stackPtr s-576) beta) :
    ∃ n u, Advances boundary n t u ∧ SelectCallState s u beta select := by
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := select_zero boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (select_zero_code state.loaded)
    (selectZeroPre_of_frame pre state rip)
  have state1 := select_zero_state pre state ready1 effect1
  have zero1 := select_zero_montgomery pre state effect1
  have copy1 := select_zero_copy pre state effect1 candidate
  have rax1 : t1.regValue .rax=if select then 1 else 0 :=
    (effect1.agrees.read (r := 0) (n := 64) (by simp [selectZeroEffect, Effect.components])).trans rax
  obtain ⟨n2,t2,run2,ready2,_,effect2⟩ := select_setup boundary pre.outerBoundary t1 ready1
    (select_setup_code state1.loaded) effect1.rip
  have mem2 := effect2.agrees.external (by simp [selectSetupEffect, Effect.components, Component.Covers])
  have state2 := state1.of_registers pre ready2 effect2.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [selectSetupEffect, Effect.components])
    (by simp [selectSetupEffect, Effect.components, Component.Covers])
  have hbyte : (((Operand.reg 0 : Operand 64).read t1).setWidth 8).setWidth 64 =
      (if select then 1 else 0 : BitVec 64) := by
    change ((t1.regValue .rax).setWidth 8).setWidth 64 = _
    rw [rax1]
    cases select <;> rfl
  refine ⟨n1+n2,t2,run1.trans run2,state2,effect2.rip,effect2.writes.2.2.2.1,
    effect2.writes.2.2.2.2.1,?_,?_,effect2.writes.2.2.2.2.2.trans hbyte,
    effect2.writes.1.trans hbyte,?_,?_⟩
  · exact effect2.writes.2.1.trans (state1.stack_address 48)
  · exact effect2.writes.2.2.1.trans (state1.stack_address 8)
  · exact Field.MontgomeryAt.of_bytes_eq zero1 (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
  · exact Field.MontgomeryAt.of_bytes_eq copy1 (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)

end P256.Proofs.Sec1.SquareRoot
