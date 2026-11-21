import P256.Proofs.Verifying.Combination.Interface
import P256.Proofs.Program.ScalarFrame.Prologue
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev State [Bindings] (s t : RamState) (offset : BitVec 64 := 6552) : Prop :=
  FrameState s t 96 8808 offset

theorem save_registers_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 6 s t ∧ State s t 48 ∧ t.RIP = 0x10650a ∧
      AgreesExcept (saveFrame s) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers pre.stack (pre.avoids (Stack.region s 8808) (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide)
      (codeOffset := 0x6500) pre.rip (by constructor <;> decide +kernel)
  have wider : AgreesExcept (saveFrame s ++ [.flags]) s t :=
    agrees.mono (by intro c hc; exact List.mem_append_left _ hc)
  exact ⟨t, run, prologue_frame pre (by decide) ready loaded rsp memory wider, rip, agrees⟩

theorem subtract_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : BitVec 64} (pre : Pre s boundary) (state : State s t offset)
    (pc : Nat) (amount : BitVec 32) (bound : pc + 7 < 118431)
    (code : Extracted.textBytes.toListFrom pc 7 = [0x48, 0x81, 0xec] ++ immBytes 32 amount)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    ∃ u, Advances boundary 1 t u ∧ State s u (offset + amount.signExtend 64) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + 7) ∧
      AgreesExcept [.reg 4, .flags, .rip] t u := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  obtain ⟨u, run, ready, effect⟩ :=
    (sub_r64_imm32_effect_step p 0x48 0xec amount
      (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) pc _ (Nat.le_of_lt bound) code)
      rip (by
        change p + 7 ≠ boundary.rip
        have he : p + 7 = Extracted.textAddress + BitVec.ofNat 64 (pc + 7) := by
          simp only [p, BitVec.ofNat_add, BitVec.add_assoc]; rfl
        rw [he]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ bound))
  have agrees : AgreesExcept [.reg 4, .flags, .rip] t u := effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have rsp : stackPtr u = stackPtr s - (offset + amount.signExtend 64) := by
    have h : stackPtr u = stackPtr t - amount.signExtend 64 := effect.writes
    rw [h, state.rsp, BitVec.sub_sub]
  refine ⟨u, run, ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear (by simp) state.directionFlag,
    fun a ha => agrees.grow a (state.allocated a ha), ?_, rsp, ?_, ?_,
    (agrees.mxcsr (by simp)).trans state.mxcsr,
    (agrees.fcw (by simp)).trans state.fp87⟩, ?_, agrees⟩
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro entry he
    rw [memory]
    exact state.saved entry he
  · change memLoad u.external _ 64 = _
    rw [memory]
    exact state.returnAddress
  · have h : u.RIP = p + 7#64 := effect.rip
    simpa only [p, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem probe_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t 4144) (rip : t.RIP = 0x106511) :
    ∃ u, Advances boundary 1 t u ∧ State s u 4144 ∧ u.RIP = 0x106519 ∧
      AgreesExcept [.mem (stackPtr s - 4144) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 .none
  have address : storeAddrAt 0x106511 am 8 t = stackPtr s - 4144 := by
    change stackPtr t + 0#64 = _
    rw [BitVec.add_zero]
    exact state.rsp
  have writable : MemWritable t (stackPtr s - 4144) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp))
      (offset := 4144) (by decide) (by decide)) state.allocated
  have apart : RangeApart (stackPtr s - 4144) 8 0x106511 8 := by
    intro i hi j hj he
    apply pre.avoids (Stack.region s 8808) (by simp)
      (stackPtr s - 4144 + BitVec.ofNat 64 i)
    · exact stack_contains pre (offset := 4144) (by decide) (by decide) ⟨i, hi, rfl⟩
    · apply Or.inl
      rw [he]
      have h := inProgram_of_textOffset (0x6511 + j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc,
        show Extracted.textAddress + BitVec.ofNat 64 0x6511 = 0x106511 from rfl] using h
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_imm32_effect_step 0x106511 0x48 (by simp [RexWPrefix]) am
      (by constructor <;> decide +kernel) rfl rfl 0).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6511 _
        (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸ apart⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6519 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 4144) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64Imm32Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x106511 am 8 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre (by decide) state ready agrees ?_ (by simp),
    effect.rip, agrees⟩
  intro c hc a covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨_, by simp, work_contains pre (offset := 4144) (by decide) (by decide) covered⟩
  · exact covered.elim

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 9 s t ∧ State s t ∧ t.RIP = 0x106520 ∧
      AgreesExcept (saveFrame s ++ [.flags, .mem (stackPtr s - 4144) 8]) s t := by
  obtain ⟨t0, run0, state0, rip0, agrees0⟩ := save_registers_frame pre
  obtain ⟨t1, run1, state1, rip1, agrees1⟩ := subtract_stack pre state0 0x650a 4096
    (by decide) (by decide +kernel) rip0
  obtain ⟨t2, run2, state2, rip2, agrees2⟩ := probe_stack pre state1 rip1
  obtain ⟨t3, run3, state3, rip3, agrees3⟩ := subtract_stack pre state2 0x6519 2408
    (by decide) (by decide +kernel) rip2
  refine ⟨t3, ((run0.trans run1).trans run2).trans run3, state3, rip3, ?_⟩
  apply (((agrees0.trans agrees1).trans agrees2).trans agrees3).mono
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  intro c hc
  rcases hc with ((h | h) | h) | h
  · exact Or.inl h
  · rcases h with rfl | rfl | rfl <;> simp
  · rcases h with rfl | rfl <;> simp
  · rcases h with rfl | rfl | rfl <;> simp

end P256.Proofs.Verifying.Combination
