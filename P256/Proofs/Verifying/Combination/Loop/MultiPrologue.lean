import P256.Proofs.Verifying.Combination.Loop.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev State [Bindings] (s t : RamState) (offset : BitVec 64 := 408) : Prop :=
  FrameState s t 96 1432 offset

theorem save_registers_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64}
    (pre : MultiPre s boundary tables digits) :
    ∃ t, Advances boundary 6 s t ∧ State s t 48 ∧ t.RIP = 0x10efda ∧
      AgreesExcept (saveFrame s) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers pre.stack (pre.avoids (Stack.region s 1432) (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide)
      (codeOffset := 0xefd0) pre.rip (by constructor <;> decide +kernel)
  have wider : AgreesExcept (saveFrame s ++ [.flags]) s t :=
    agrees.mono (by intro c hc; exact List.mem_append_left _ hc)
  exact ⟨t, run, prologue_frame pre.toCalleePre (by decide) ready loaded rsp memory wider, rip, agrees⟩

theorem subtract_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64}
    {offset : BitVec 64} (pre : MultiPre s boundary tables digits) (state : State s t offset)
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

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits) :
    ∃ t, Advances boundary 7 s t ∧ State s t ∧ t.RIP = 0x10efe1 ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨a, runA, stateA, ripA, agreesA⟩ := save_registers_frame pre
  obtain ⟨t, runT, stateT, ripT, agreesT⟩ := subtract_stack pre stateA 0xefda 360
    (by decide) (by decide +kernel) ripA
  refine ⟨t, runA.trans runT, stateT, ripT, ?_⟩
  apply (agreesA.trans agreesT).mono
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  intro c hc
  rcases hc with h | rfl | rfl | rfl
  · exact Or.inl h
  all_goals simp

end P256.Proofs.Verifying.Combination.Loop.Multi
