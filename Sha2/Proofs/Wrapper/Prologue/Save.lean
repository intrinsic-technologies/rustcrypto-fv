import Sha2.Proofs.Wrapper.Prologue.Push

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Prologue

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize

structure Result [Bindings] (initial s : RamState) (v : Variant := .sha256) : Prop extends State initial s v where
  rip : s.RIP = (v.pc 0x11)
  rsp : stackPtr s = stackPtr initial - 344
  arguments : ∀ register ∈ [Syntax.Reg.rdi, .rsi, .rdx, .rcx],
    s.regValue register = initial.regValue register

theorem save_registers {v : Variant} [Bindings] {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) :
    ∃ s, State initial s v ∧ s.RIP = (v.pc 0xa) ∧ stackPtr s = stackPtr initial - 48 ∧
      AgreesExcept (saveFrame initial) initial s := by
  have push : PushSteps initial (returnBoundary initial) := ⟨by
    intro t ready loaded grow src offset codeOffset sp ip bound align size bytes
    exact push_exists ctx ready loaded grow src offset codeOffset sp ip (by omega) align size bytes⟩
  obtain ⟨s, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    save_registers_of_push push (supportedMachine_readyToStep ctx.machine)
      ctx.call.programLoaded (codeOffset := (v.textOffset + 0x0)) ctx.call.entry
      (by cases v <;> constructor <;> decide +kernel)
  refine ⟨s, ?_, rip, rsp, frame⟩
  refine ⟨⟨6, run⟩, supportedMachine_of_ready_agrees ctx.machine ready frame,
    loaded, frame.grow, ?_, frame.directionFlagClear (by simp [saveFrame]) ctx.call.directionFlagUnset, ?_⟩
  · constructor
    · intro slot hs
      rw [memory]
      exact saveMemory_saved initial slot hs
    · rw [memory]
      simp only [saveMemory, BitVec.sub_eq_add_neg]
      repeat rw [memLoad_memStore_apart_right _ (stackPtr initial) _ _ 64
        (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide) (by cases v <;> decide)]
  · apply frame.memoryWriteFrame
    intro c hc a ha
    simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial v.routine.minStackBytes, by simp, ?_⟩
    all_goals exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by cases v <;> decide) (by cases v <;> decide) ha

theorem run {v : Variant} [Bindings] {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) : ∃ s, Result initial s v := by
  obtain ⟨saved, state, rip, rsp, frame⟩ := save_registers ctx
  obtain ⟨s, step, ready, effect⟩ :=
    (sub_r64_imm32_effect_step (v.pc 0xa) 0x48 0xec 296
      (by constructor <;> decide) (by cases v <;> decide) (by cases v <;> decide)).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) (v.textOffset + 0xa)
        [0x48,0x81,0xec,0x28,1,0,0] (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by
        change v.pc 0xa + BitVec.ofNat 64 7 ≠ (returnBoundary initial).rip
        rw [Variant.pc_add]
        exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
            (v.pc_inProgram (offset := 0x11) (by decide)))
  have agrees : AgreesExcept [.reg 4, .flags, .rip] saved s := effect.agrees
  have result := state.of_agrees ctx step ready agrees (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ha.elim) (by
    intro c hc a _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact id)
  refine ⟨s, ⟨result, ?_, ?_, ?_⟩⟩
  · have hrip := effect.rip
    change s.RIP = v.pc 0xa + BitVec.ofNat 64 7 at hrip
    rwa [Variant.pc_add] at hrip
  · have value : stackPtr s = stackPtr saved - 296 := effect.writes
    rw [value, rsp, BitVec.sub_sub]
    rfl
  · intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact (agrees.read (n := 64) (r := 7) (by simp)).trans
          (frame.read (n := 64) (r := 7) (by simp [saveFrame]))
      | exact (agrees.read (n := 64) (r := 6) (by simp)).trans
          (frame.read (n := 64) (r := 6) (by simp [saveFrame]))
      | exact (agrees.read (n := 64) (r := 2) (by simp)).trans
          (frame.read (n := 64) (r := 2) (by simp [saveFrame]))
      | exact (agrees.read (n := 64) (r := 1) (by simp)).trans
          (frame.read (n := 64) (r := 1) (by simp [saveFrame]))

end Sha2.Proofs.Wrapper.Prologue
