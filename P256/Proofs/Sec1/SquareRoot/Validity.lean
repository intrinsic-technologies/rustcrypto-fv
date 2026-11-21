import P256.Proofs.Sec1.SquareRoot.State
import P256.Proofs.Sec1.SquareRoot.CompareValue
import P256.Proofs.Common.Instructions.Setb.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setccValue setcc_r8_rex_effect_step)
open P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem comparePre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11450a) : ComparePre t := by
  refine ⟨rip, ?_⟩
  intro i hi
  rw [state.stack_address]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [BitVec.reduceSub]
  all_goals exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated

theorem validity_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11450a) (hx : MontgomeryAt t (stackPtr s - 392) x)
    (hy : MontgomeryAt t (stackPtr s - 536) y) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11454d ∧
      u.regValue .rdi = (if x=y then 1 else 0) ∧ u.external = t.external := by
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := compare_square boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (compare_code state.loaded)
    (comparePre_of_frame pre state rip)
  have state1 := state.of_registers pre ready1 effect1.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [compareEffect, Effect.components])
    (by simp [compareEffect, Effect.components, Component.Covers])
  have zero : compareWord t=0 ↔ x=y := compareWord_eq_zero (by
    change MontgomeryAt t ((Operand.reg 4 : Operand 64).read t+192) x
    rw [state.stack_address]; exact hx) (by
    change MontgomeryAt t ((Operand.reg 4 : Operand 64).read t+48) y
    rw [state.stack_address]; exact hy)
  have hzf : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = decide (x=y) := by
    have h := effect1.flags
    have hz := h.2.2.2.1
    change (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = (compareWord t == 0) at hz
    rw [hz]
    exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq, decide_eq_true_eq] using zero)
  have hdi : t1.GPR[gprIndex 7] = (0 : BitVec 64) := effect1.writes.2.2.2.2
  have step : StepEffect (fun s => s.RIP=0x114549)
      (codeRange 0x114549 [0x40,0x0f,0x94,0xc7]) (setccR8Effect 0x114549 4 7 4) :=
    setcc_r8_rex_effect_step 0x114549 0x40 0x94 0xc7 (by simp [RexPrefix]) (by simp [SupportedOpcode]) rfl
  obtain ⟨t2,run2,ready2,effect2⟩ := step.advances ready1
    (programText_slice (programLoaded_codeIn state1.loaded) 0x14549 _ (by decide +kernel) (by decide +kernel))
    effect1.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1454d (by decide)))
  have state2 := state1.of_registers pre ready2 effect2.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [setccR8Effect_components])
    (by simp [setccR8Effect_components, Component.Covers])
  refine ⟨n1+1,t2,run1.trans run2,state2,effect2.rip,?_,?_⟩
  · have hv := effect2.writes
    change t2.regValue .rdi = mergeGPR 8 (setccValue 4 t1) t1.GPR[gprIndex 7] at hv
    rw [hv,hdi]
    change mergeGPR 8 (if (StatusFlags.ofRFLAGS t1.RFLAGS).ZF then 1 else 0) 0 = _
    rw [hzf]
    simp only [decide_eq_true_eq]
    split <;> rfl
  · exact (effect2.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans
      (effect1.agrees.external (by simp [compareEffect, Effect.components, Component.Covers]))

end P256.Proofs.Sec1.SquareRoot
